package main

import (
	"bytes"
	"fmt"
	"go/format"
	"os"
)

// reorderFile orchestrates reading the file, running analysis, and emitting the
// reordered output. Splitting the phases keeps each file small and focused.
func reorderFile(filename string, dry bool) error {
	src, err := readSource(filename)
	if err != nil {
		return err
	}

	out, err := buildReordered(filename, src)
	if err != nil {
		return err
	}

	if dry {
		return writeDry(out)
	}

	return writeIfChanged(filename, src, out)
}

// readSource reads the file content and returns the bytes or an error.
func readSource(filename string) ([]byte, error) {
	src, err := os.ReadFile(filename)
	if err != nil {
		fmt.Fprintf(os.Stderr, "read error: %v\n", err)

		return nil, err
	}

	return src, nil
}

// buildReordered analyses and produces reordered output bytes (unformatted on failure to format).
func buildReordered(filename string, src []byte) ([]byte, error) {
	a, err := analyzeFile(filename, src)
	if err != nil {
		return nil, err
	}

	out := buildOutput(a)
	candidate := out
	if formatted, ferr := format.Source(out); ferr == nil {
		candidate = formatted
	}

	// Guard: ensure we never reduce the number of non-blank lines. If the
	// candidate output has fewer non-blank lines than the original source,
	// fall back to the original content to avoid accidental deletion.
	if nonBlankLineCount(candidate) < nonBlankLineCount(src) {
		candidate = formatMaybe(src)
	}

	return candidate, nil
}

// nonBlankLineCount counts lines with non-whitespace content.
func nonBlankLineCount(b []byte) int {
	count := 0
	start := 0
	for start <= len(b) {
		end := start
		for end < len(b) && b[end] != '\n' {
			end++
		}
		// trim spaces and tabs; treat pure whitespace as blank
		lineHasNonSpace := false
		for i := start; i < end; i++ {
			if b[i] != ' ' && b[i] != '\t' && b[i] != '\r' {
				lineHasNonSpace = true
				break
			}
		}
		if lineHasNonSpace {
			count++
		}
		if end == len(b) {
			break
		}
		start = end + 1
	}
	return count
}

// writeDry writes output bytes to stdout and ensures a trailing newline.
func writeDry(out []byte) error {
	if _, err := os.Stdout.Write(out); err != nil {
		return err
	}

	if len(out) == 0 || out[len(out)-1] != '\n' { // only add newline if missing
		if _, err := os.Stdout.Write([]byte("\n")); err != nil {
			return err
		}
	}

	return nil
}

// writeIfChanged compares formatted versions of original and output and writes only if different.
func writeIfChanged(filename string, orig, out []byte) error {
	formattedOrig := formatMaybe(orig)

	formattedOut := formatMaybe(out)
	if len(formattedOrig) == len(formattedOut) && bytes.Equal(formattedOrig, formattedOut) {
		return nil
	}

	return writeFile(filename, formattedOut)
}

// formatMaybe returns go/format output or the input on failure.
func formatMaybe(src []byte) []byte {
	if f, err := format.Source(src); err == nil {
		return f
	}

	return src
}

// writeFile writes the bytes to filename using secure permissions.
func writeFile(filename string, out []byte) error {
	const outFilePerm = 0600
	if err := os.WriteFile(filename, out, outFilePerm); err != nil {
		fmt.Fprintf(os.Stderr, "failed to write updated file: %v\n", err)

		return err
	}

	return nil
}
