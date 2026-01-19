#!/bin/bash

# Strict mode with error reporting
set -euo pipefail
trap 's=$?; echo "$0: Error on line "$LINENO": $BASH_COMMAND"; exit $s' ERR
IFS=$'\n\t'

REPORT_LOCATION="target/coverage"

# add llvm tools necessary for code analysis
rustup component add llvm-tools

# check if grcov is installed, if not install it
if ! command -v grcov > /dev/null
then
    # Temporarily set the version to 0.8.20 to failing installation because of
    # yanked zip dependency
    cargo install grcov
fi

# clean build files (otherwise the coverage report might be flaky)
cargo clean

# Create output directory
mkdir -p target
mkdir -p target/coverage

# Execute tests with coverage flags
RUSTFLAGS="-C instrument-coverage" \
    cargo test --all-features

# Execute doc tests
RUSTFLAGS="-C instrument-coverage" \
    cargo test --doc

# Generate coverage report with grcov
grcov . --binary-path ./target/debug/deps \
        -s . \
        -t html,cobertura,markdown \
        --branch --ignore-not-existing --ignore '../*' --ignore "/*"\
        --ignore '*/test/*' --ignore '*/tests/*'\
        --excl-line '#\[*|}|debug_assert!*|unreachable!*|exit\(*\);*' \
        -o ${REPORT_LOCATION}

# Remove profiling files
find . -name "*.profraw" -type f -delete

echo "Finished Generating Coverage Report"

(open "${PWD}/${REPORT_LOCATION}/html/index.html" &> /dev/null) \
    || (xdg-open "${PWD}/${REPORT_LOCATION}/html/index.html" &> /dev/null) \
    || (echo "You can find the report under ${PWD}/${REPORT_LOCATION}/html/index.html" && exit 0)
