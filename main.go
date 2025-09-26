package main

import (
	"errors"
	"flag"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
)

var (
	ErrDryModeDirectory = errors.New("-dry mode requires a single .go file, not a directory")
	ErrProcessingFiles  = errors.New("errors while processing files")
)

func main() {
	dry := flag.Bool("dry", false, "dry run: print full altered file then summary; without, write in place")
	flag.Parse()
	args := flag.Args()

	if len(args) != 1 {
		fmt.Fprintf(os.Stderr, "usage: reorder <file.go>\n")

		const usageExit = 2
		os.Exit(usageExit)
	}

	target := args[0]

	if err := processTarget(target, *dry); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

// processTarget handles a target file or directory.
//
//nolint:gocyclo // dispatcher is simple branching for CLI; refactor would add noise
func processTarget(target string, dry bool) error {
	info, err := os.Stat(target)
	if err == nil && info.IsDir() && dry {
		return ErrDryModeDirectory
	}

	if err == nil && info.IsDir() && !dry {
		return processDirectory(target)
	}

	if err := reorderFile(target, dry); err != nil {
		return err
	}

	return nil
}

func processDirectory(target string) error {
	var failed []string

	walkErr := filepath.WalkDir(target, makeWalkFunc(&failed))
	if walkErr != nil {
		return fmt.Errorf("error walking directory: %w", walkErr)
	}

	if len(failed) > 0 {
		return fmt.Errorf("%w: %d errors", ErrProcessingFiles, len(failed))
	}

	return nil
}

//nolint:gocognit,gocyclo // traversal helper; complexity is primarily branching
func makeWalkFunc(failed *[]string) func(string, fs.DirEntry, error) error {
	return func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			// record and continue
			*failed = append(*failed, path+": "+err.Error())

			return nil //nolint:nilerr // intentionally continue on walk error
		}

		// Skip directories we don't want to descend into
		if d.IsDir() {
			base := filepath.Base(path)
			if base == ".git" || base == "vendor" || base == "node_modules" {
				return filepath.SkipDir
			}

			return nil
		}

		if strings.HasSuffix(path, ".go") && !strings.HasSuffix(path, "_test.go") {
			if err := reorderFile(path, false); err != nil {
				*failed = append(*failed, path+": "+err.Error())
			}
		}

		return nil
	}
}
