#! /bin/bash
# Strict mode with error reporting
set -euo pipefail
trap 's=$?; echo "$0: Error on line "$LINENO": $BASH_COMMAND"; exit $s' ERR
IFS=$'\n\t'

# Markdown document the index page will be generated from (without file ending)
INDEX_PAGE_FILE_NAME="dev-docs"
INDEX_PAGE_FILE_LOCATION="./docs"

# Output directory of generated documentation
OUTPUT_LOCATION="target/doc"

# Check if nightly toolchain is installed, if not install it
if ! command -v cargo +nightly --version > /dev/null
then
    echo "Our documentation uses unstable features. Installing nightly Rust"
    rustup toolchain install nightly
fi

rm -rf  "${OUTPUT_LOCATION}"

echo "Generating documentation..."
RUSTDOCFLAGS="--index-page=${INDEX_PAGE_FILE_LOCATION}/${INDEX_PAGE_FILE_NAME}.md -Zunstable-options" cargo +nightly doc --no-deps --document-private-items --workspace

# Open the index page
(open "${PWD}/${OUTPUT_LOCATION}/${INDEX_PAGE_FILE_NAME}.html" &> /dev/null) \
    || (xdg-open "${PWD}/${OUTPUT_LOCATION}/${INDEX_PAGE_FILE_NAME}.html" &> /dev/null) \
    || (echo "You can find the report under ${PWD}/${OUTPUT_LOCATION}/${INDEX_PAGE_FILE_NAME}.html" && exit 0)
