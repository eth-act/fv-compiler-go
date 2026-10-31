// Native side of the semantics difftest (issue #10, docs/plans/semantics.md §9): integer and
// boolean functions in the P1 subset (no memory, no calls besides the runtime's panicking
// entry points), and a harness that reads calls from stdin, one per line
//
//	<func> <arg>...
//
// and prints, for each, one line
//
//	<func> <arg>... -> returned <result>...
//	<func> <arg>... -> panicked <runtime.Error text>
//
// Built with the patched toolchain for linux/arm64 under GOFV_SSA_EXPORT, so the binary run
// under qemu-aarch64-static is compiled from exactly the exported SSA. The function list is
// in funcs.go; scripts/sem-difftest.sh drives both sides.
package main

import (
	"bufio"
	"fmt"
	"os"
	"reflect"
	"strconv"
	"strings"
)

func parseArg(t reflect.Type, s string) (reflect.Value, error) {
	v := reflect.New(t).Elem()
	switch t.Kind() {
	case reflect.Bool:
		b, err := strconv.ParseBool(s)
		v.SetBool(b)
		return v, err
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		n, err := strconv.ParseInt(s, 10, t.Bits())
		v.SetInt(n)
		return v, err
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		n, err := strconv.ParseUint(s, 10, t.Bits())
		v.SetUint(n)
		return v, err
	}
	return v, fmt.Errorf("unsupported parameter type %s", t)
}

func render(v reflect.Value) string {
	switch v.Kind() {
	case reflect.Bool:
		return strconv.FormatBool(v.Bool())
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return strconv.FormatInt(v.Int(), 10)
	default:
		return strconv.FormatUint(v.Uint(), 10)
	}
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
	parts := make([]string, len(res))
	for i, r := range res {
		parts[i] = render(r)
	}
	return strings.TrimRight("returned "+strings.Join(parts, " "), " ")
}

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<20)
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	for in.Scan() {
		line := in.Text()
		f := strings.Fields(line)
		if len(f) == 0 {
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
			a, err := parseArg(ft.In(i), f[i+1])
			if err != nil {
				fmt.Fprintf(os.Stderr, "%s: argument %d: %v\n", f[0], i, err)
				os.Exit(2)
			}
			args[i] = a
		}
		fmt.Fprintf(w, "%s -> %s\n", line, call(fv, args))
	}
}
