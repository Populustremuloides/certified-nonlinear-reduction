#!/bin/sh
# Compile this self-contained project using the installed TeX Live distribution.
set -eu
cd "$(dirname "$0")"
paper_root="$(pwd -P)"
mkdir -p output/pdf build
export TEXINPUTS="$paper_root:${TEXINPUTS:-}"
export TFMFONTS="$paper_root/fonts//:${TFMFONTS:-}"
export T1FONTS="$paper_root/fonts//:${T1FONTS:-}"

if command -v pdflatex >/dev/null 2>&1; then
    tex_engine="$(command -v pdflatex)"
elif [ -x /Library/TeX/texbin/pdflatex ]; then
    tex_engine=/Library/TeX/texbin/pdflatex
else
    printf '%s\n' 'pdfLaTeX was not found. Install TeX Live or MacTeX, then try again.' >&2
    exit 127
fi

for pass in 1 2; do
    log="build/paper_pass${pass}.log"
    if ! "$tex_engine" -interaction=nonstopmode -halt-on-error -file-line-error \
        -synctex=1 -recorder -output-directory=output/pdf -jobname=paper_complete \
        '\pdfmapfile{+fonts/rsfs.map}\input{main.tex}' > "$log" 2>&1; then
        cat "$log"
        exit 1
    fi
done
printf 'Compiled: %s/output/pdf/paper_complete.pdf\n' "$paper_root"

# Regenerate the submission pair when a Python interpreter with pypdf is available.
l4dc_pdf_python=""
for candidate in "${L4DC_PDF_PYTHON:-}" python3 "$HOME/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3"; do
    [ -n "$candidate" ] || continue
    if command -v "$candidate" >/dev/null 2>&1 && "$candidate" -c 'import pypdf' >/dev/null 2>&1; then
        l4dc_pdf_python="$candidate"
        break
    fi
done
if [ -n "$l4dc_pdf_python" ]; then
    "$l4dc_pdf_python" prepare_submission.py
else
    printf '%s\n' 'To generate the main/supplement PDFs, install pypdf and run python3 prepare_submission.py.'
fi
