#!/bin/bash
# Throwaway: print the files (from a list) whose last stock section before `lower` has an OpInvalid value.
while read -r f; do
  awk '/^pass [0-9]+ "lower"/{exit} /^pass /{c=0} $1=="v" && $3=="OpInvalid"{c++} END{if (c>0) print FILENAME}' "$f"
done < "$1"
