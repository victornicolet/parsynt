#!/bin/sh

PROJECT_DIR=$(pwd)

echo "Updating conf ..."
rm ./src/conf/project_dir.ml
echo "let base = \"$PROJECT_DIR\"" >> ./src/conf/project_dir.ml
echo "let src = \"$PROJECT_DIR/src\"" >> ./src/conf/project_dir.ml
