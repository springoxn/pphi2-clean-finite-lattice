ENTRY
  { address author booktitle edition howpublished journal note number pages publisher series title volume year }
  {}
  {}

FUNCTION {begin.bib}
{ "\begin{thebibliography}{99}" write$ newline$ }

FUNCTION {end.bib}
{ "\end{thebibliography}" write$ newline$ }

FUNCTION {bibitem}
{ "\bibitem{" cite$ * "}" * write$ newline$ }

FUNCTION {article}
{
  bibitem
  author write$ ". " write$
  title write$ ". " write$
  "\emph{" write$ journal write$ "} " write$
  volume write$
  number empty$ { skip$ } { "(" write$ number write$ ")" write$ } if$
  pages empty$ { skip$ } { ":" write$ pages write$ } if$
  ", " write$ year write$ ". " write$ note write$ newline$
}

FUNCTION {book}
{
  bibitem
  author write$ ". \emph{" write$ title write$ "}. " write$
  edition empty$ { skip$ } { edition write$ " edition. " write$ } if$
  publisher write$ ", " write$ year write$ ". " write$ note write$ newline$
}

FUNCTION {inproceedings}
{
  bibitem
  author write$ ". " write$ title write$ ". In \emph{" write$ booktitle write$ "}. " write$
  series empty$ { skip$ } { series write$ " " write$ volume write$ ". " write$ } if$
  pages empty$ { skip$ } { "pp. " write$ pages write$ ". " write$ } if$
  publisher empty$ { skip$ } { publisher write$ ", " write$ } if$
  year write$ ". " write$ note write$ newline$
}

FUNCTION {misc}
{
  bibitem
  author write$ ". " write$ title write$ ". " write$
  howpublished write$ ", " write$ year write$ ". " write$ note write$ newline$
}

FUNCTION {default.type} { misc }

READ
EXECUTE {begin.bib}
ITERATE {call.type$}
EXECUTE {end.bib}
