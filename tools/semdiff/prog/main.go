// Native side of the semantics difftest (issue #10, docs/plans/semantics.md §9): functions in
// the P1 (funcs.go) and P2 (mem.go) subsets, and a harness that reads calls from stdin, one per
// line, fields separated by tabs:
//
//	<func>\t<arg>\t<arg>...
//
// and prints, for each, one line
//
//	<call> -> returned\t<result>...\t||\t<arg after the call>...
//	<call> -> panicked <runtime.Error text>
//
// Values are written in a small syntax shared with GoFVTest/SemDiff.lean: integers in decimal,
// floats as their IEEE bit patterns in hex (0x3ff0000000000000; NaN payloads exact),
// complex numbers {re,im}, true/false, strings Go-quoted, slices nil or [e,...], arrays
// [e,...], structs {f,...}, pointers nil or &e. The arguments are printed again after the call, so writes through
// pointers and slices are compared too.
//
// Built with the patched toolchain for linux/arm64 under GOFV_SSA_EXPORT, so the binary run
// under qemu-aarch64-static is compiled from exactly the exported SSA; scripts/sem-difftest.sh
// drives both sides.
package main

import (
	"bufio"
	"fmt"
	"os"
	"reflect"
	"strconv"
	"strings"
	"unsafe"
)

type parser struct {
	s string
	i int
}

func (p *parser) fail(what string) error {
	return fmt.Errorf("at %d of %q: %s", p.i, p.s, what)
}

func (p *parser) eat(c byte) bool {
	if p.i < len(p.s) && p.s[p.i] == c {
		p.i++
		return true
	}
	return false
}

func (p *parser) word() string {
	j := p.i
	for p.i < len(p.s) && !strings.ContainsRune(",]}", rune(p.s[p.i])) {
		p.i++
	}
	return p.s[j:p.i]
}

// list parses e,e,...close (the opening bracket already consumed).
func (p *parser) list(close byte, elem func() error) error {
	if p.eat(close) {
		return nil
	}
	for {
		if err := elem(); err != nil {
			return err
		}
		if p.eat(close) {
			return nil
		}
		if !p.eat(',') {
			return p.fail("expected , or close")
		}
	}
}

func (p *parser) parse(t reflect.Type) (reflect.Value, error) {
	v := reflect.New(t).Elem()
	switch t.Kind() {
	case reflect.Bool:
		b, err := strconv.ParseBool(p.word())
		v.SetBool(b)
		return v, err
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		n, err := strconv.ParseInt(p.word(), 10, t.Bits())
		v.SetInt(n)
		return v, err
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		n, err := strconv.ParseUint(p.word(), 10, t.Bits())
		v.SetUint(n)
		return v, err
	case reflect.Float32, reflect.Float64:
		// bits written through memory: reflect's SetFloat converts through float64, which
		// would quieten a float32 signalling NaN
		n, err := strconv.ParseUint(p.word(), 0, t.Bits())
		if t.Kind() == reflect.Float32 {
			*(*uint32)(v.Addr().UnsafePointer()) = uint32(n)
		} else {
			*(*uint64)(v.Addr().UnsafePointer()) = n
		}
		return v, err
	case reflect.Complex64, reflect.Complex128:
		if !p.eat('{') {
			return v, p.fail("expected {")
		}
		half := t.Bits() / 2
		var parts []uint64
		err := p.list('}', func() error {
			n, err := strconv.ParseUint(p.word(), 0, half)
			parts = append(parts, n)
			return err
		})
		if err == nil && len(parts) != 2 {
			err = p.fail("complex needs 2 parts")
		}
		if err == nil {
			ptr := v.Addr().UnsafePointer()
			if half == 32 {
				*(*uint32)(ptr) = uint32(parts[0])
				*(*uint32)(unsafe.Add(ptr, 4)) = uint32(parts[1])
			} else {
				*(*uint64)(ptr) = parts[0]
				*(*uint64)(unsafe.Add(ptr, 8)) = parts[1]
			}
		}
		return v, err
	case reflect.String:
		q, err := strconv.QuotedPrefix(p.s[p.i:])
		if err != nil {
			return v, p.fail("bad string")
		}
		p.i += len(q)
		s, err := strconv.Unquote(q)
		v.SetString(s)
		return v, err
	case reflect.Slice:
		if strings.HasPrefix(p.s[p.i:], "nil") {
			p.i += 3
			return v, nil
		}
		if !p.eat('[') {
			return v, p.fail("expected [")
		}
		var es []reflect.Value
		err := p.list(']', func() error {
			e, err := p.parse(t.Elem())
			es = append(es, e)
			return err
		})
		v.Set(reflect.MakeSlice(t, len(es), len(es)))
		for i, e := range es {
			v.Index(i).Set(e)
		}
		return v, err
	case reflect.Array:
		if !p.eat('[') {
			return v, p.fail("expected [")
		}
		i := 0
		err := p.list(']', func() error {
			e, err := p.parse(t.Elem())
			if i < t.Len() {
				v.Index(i).Set(e)
			}
			i++
			return err
		})
		if err == nil && i != t.Len() {
			err = p.fail("array length")
		}
		return v, err
	case reflect.Struct:
		if !p.eat('{') {
			return v, p.fail("expected {")
		}
		i := 0
		err := p.list('}', func() error {
			e, err := p.parse(t.Field(i).Type)
			v.Field(i).Set(e)
			i++
			return err
		})
		return v, err
	case reflect.Pointer:
		if strings.HasPrefix(p.s[p.i:], "nil") {
			p.i += 3
			return v, nil
		}
		if !p.eat('&') {
			return v, p.fail("expected &")
		}
		e, err := p.parse(t.Elem())
		ptr := reflect.New(t.Elem())
		ptr.Elem().Set(e)
		v.Set(ptr)
		return v, err
	}
	return v, fmt.Errorf("unsupported type %s", t)
}

// quoteBytes is strconv.Quote byte by byte: printable ASCII as is, the usual escapes, every
// other byte as \xHH (also inside valid UTF-8), as GoFVTest/SemDiff.lean's goQuote prints.
func quoteBytes(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c == '"' || c == '\\':
			b.WriteByte('\\')
			b.WriteByte(c)
		case c >= 0x20 && c < 0x7f:
			b.WriteByte(c)
		default:
			q := strconv.QuoteToASCII(string([]byte{c}))
			if c >= 0x80 {
				q = fmt.Sprintf("\"\\x%02x\"", c)
			}
			b.WriteString(q[1 : len(q)-1])
		}
	}
	b.WriteByte('"')
	return b.String()
}

// bitsOf reads the n-byte bit pattern at byte offset off of v (copied into memory first: a
// float32 read through reflect's Float converts through float64).
func bitsOf(v reflect.Value, off uintptr, n int) uint64 {
	c := reflect.New(v.Type())
	c.Elem().Set(v)
	ptr := unsafe.Add(c.UnsafePointer(), off)
	if n == 4 {
		return uint64(*(*uint32)(ptr))
	}
	return *(*uint64)(ptr)
}

func render(v reflect.Value) string {
	switch v.Kind() {
	case reflect.Float32:
		return fmt.Sprintf("0x%08x", bitsOf(v, 0, 4))
	case reflect.Float64:
		return fmt.Sprintf("0x%016x", bitsOf(v, 0, 8))
	case reflect.Complex64:
		return fmt.Sprintf("{0x%08x,0x%08x}", bitsOf(v, 0, 4), bitsOf(v, 4, 4))
	case reflect.Complex128:
		return fmt.Sprintf("{0x%016x,0x%016x}", bitsOf(v, 0, 8), bitsOf(v, 8, 8))
	case reflect.Bool:
		return strconv.FormatBool(v.Bool())
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return strconv.FormatInt(v.Int(), 10)
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		return strconv.FormatUint(v.Uint(), 10)
	case reflect.String:
		return quoteBytes(v.String())
	case reflect.Slice, reflect.Array:
		if v.Kind() == reflect.Slice && v.IsNil() {
			return "nil"
		}
		parts := make([]string, v.Len())
		for i := range parts {
			parts[i] = render(v.Index(i))
		}
		return "[" + strings.Join(parts, ",") + "]"
	case reflect.Struct:
		parts := make([]string, v.NumField())
		for i := range parts {
			parts[i] = render(v.Field(i))
		}
		return "{" + strings.Join(parts, ",") + "}"
	case reflect.Pointer:
		if v.IsNil() {
			return "nil"
		}
		return "&" + render(v.Elem())
	}
	return "<" + v.Type().String() + ">"
}

func call(fn reflect.Value, args []reflect.Value) (out string) {
	defer func() {
		if r := recover(); r != nil {
			if e, ok := r.(error); ok {
				out = "panicked " + e.Error()
			} else {
				out = fmt.Sprintf("panicked %v", r)
			}
		}
	}()
	res := fn.Call(args)
	parts := []string{"returned"}
	for _, r := range res {
		parts = append(parts, render(r))
	}
	parts = append(parts, "||")
	for _, a := range args {
		parts = append(parts, render(a))
	}
	return strings.Join(parts, "\t")
}

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<20)
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	for in.Scan() {
		line := in.Text()
		f := strings.Split(line, "\t")
		if line == "" {
			continue
		}
		fn, ok := funcs[f[0]]
		if !ok {
			fmt.Fprintf(os.Stderr, "unknown function %s\n", f[0])
			os.Exit(2)
		}
		fv := reflect.ValueOf(fn)
		ft := fv.Type()
		if ft.NumIn() != len(f)-1 {
			fmt.Fprintf(os.Stderr, "%s: %d arguments, want %d\n", f[0], len(f)-1, ft.NumIn())
			os.Exit(2)
		}
		args := make([]reflect.Value, ft.NumIn())
		for i := range args {
			p := &parser{s: f[i+1]}
			a, err := p.parse(ft.In(i))
			if err == nil && p.i != len(p.s) {
				err = p.fail("trailing input")
			}
			if err != nil {
				fmt.Fprintf(os.Stderr, "%s: argument %d: %v\n", f[0], i, err)
				os.Exit(2)
			}
			args[i] = a
		}
		fmt.Fprintf(w, "%s -> %s\n", line, call(fv, args))
	}
}
