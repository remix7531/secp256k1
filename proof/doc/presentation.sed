# Source notices and section dividers are not part of the rendered argument.
s@<span class="comment">\(\*&nbsp;Copyright[^<]*SPDX-License-Identifier:&nbsp;MIT&nbsp;\*\)</span><br/>@@g
s@<span class="comment">\(\*&nbsp;[=-]{5,}&nbsp;\*\)</span><br/>@@g
# Rocq doc uses line breaks for spacing at the edges of code containers.
s@(<div class="code">)([[:space:]]|<br/>)*@\1\n@g
s@(<br/>[[:space:]]*)+</div>@\n</div>@g
s@<div class="code">[[:space:]]*</div>@@g
