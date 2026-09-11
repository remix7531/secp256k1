#!/usr/bin/env bash
set -euo pipefail

mkdir -p html
coqdoc_directory=$(mktemp -d html/.coqdoc.XXXXXX)
trap 'rm -rf "$coqdoc_directory"' EXIT

# Keep inline expressions in one span so CSS controls their font.
rocq doc --html --body-only --parse-comments --no-index --no-lib-name -s --latin1 \
  --inline-notmono --coqlib_url https://rocq-prover.org/doc/V9.0.1/corelib \
  -Q . secp256k1 -d "$coqdoc_directory" specification.v

sed -Ez -f doc/presentation.sed "$coqdoc_directory/secp256k1.specification.html" \
  > "$coqdoc_directory/rendered.html"
: > "$coqdoc_directory/appendix.html"

# Move whole doc containers so the source offsets and symbol links stay intact.
awk -v main_file="$coqdoc_directory/main.html" \
    -v appendix_file="$coqdoc_directory/appendix.html" '
  /<!-- begin appendix -->/ {
    if (appendix || previous !~ /^<div class="doc">$/) {
      print "invalid appendix opening" > "/dev/stderr"
      exit 1
    }
    appendix = 1
  }
  {
    if (buffered) print previous > (appendix ? appendix_file : main_file)
    previous = $0
    buffered = 1
  }
  /<!-- end appendix -->/ {
    if (!appendix) {
      print "appendix closing without opening" > "/dev/stderr"
      exit 1
    }
    closing = 1
  }
  closing && /<\/div>/ {
    print previous > appendix_file
    buffered = appendix = closing = 0
  }
  END {
    if (appendix) {
      print "unterminated appendix" > "/dev/stderr"
      exit 1
    }
    if (buffered) print previous > main_file
  }
' "$coqdoc_directory/rendered.html"

{
  cat "$coqdoc_directory/main.html"
  printf '<a id="appendix-word-operations"></a>\n'
  cat "$coqdoc_directory/appendix.html"
} > "$coqdoc_directory/body.html"

awk '
  BEGIN { print "<div id=\"toc\"><ul class=\"doclist\">"; level = 1 }
  match($0, /<a id="([^"]+)"><\/a><h([1-6]) class="section">(.*)<\/h[1-6]>/, heading) {
    next_level = heading[2] + 0
    if (next_level > level + 1 || (!seen && next_level != 1)) {
      print "invalid contents heading level" > "/dev/stderr"
      exit 1
    }
    if (seen && next_level > level) print "<ul class=\"doclist\">"
    else if (seen) {
      print "</li>"
      while (level > next_level) { print "</ul></li>"; level-- }
    }
    printf "<li><a href=\"#%s\">%s</a>\n", heading[1], heading[3]
    level = next_level
    seen = 1
  }
  END {
    if (!seen) { print "no section headings" > "/dev/stderr"; exit 1 }
    print "</li>"
    while (level > 1) { print "</ul></li>"; level-- }
    print "</ul></div>"
  }
' "$coqdoc_directory/body.html" > "$coqdoc_directory/toc.html"

{
  cat doc/header.html "$coqdoc_directory/toc.html"
  printf '</nav>\n<main id="main">\n'
  cat "$coqdoc_directory/body.html" doc/footer.html
} > "$coqdoc_directory/assembled.html"

mv "$coqdoc_directory/assembled.html" html/secp256k1.specification.html
cp doc/style.css html/coqdoc.css
cp specification.v html/specification.v
