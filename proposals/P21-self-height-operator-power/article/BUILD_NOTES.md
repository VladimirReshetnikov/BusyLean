# Article build notes

The PDF was compiled from
`contender14_self_height_fd_operator_power.tex` with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  contender14_self_height_fd_operator_power.tex
```

Final checks performed in the package-building container:

- 16 pages, US Letter, unencrypted, all fonts embedded;
- no unresolved citation or cross-reference warning;
- no overfull box warning in the final LaTeX log;
- rendered at 150 DPI with the OpenAI PDF skill renderer;
- all 16 rendered pages visually inspected as a montage, with the title page,
  full-source listings, theorem inventory, and final references inspected at
  larger scale;
- text extraction spot-checked with `pdftotext`;
- preflight opened successfully with PyMuPDF and found no forms, XFA, or
  encryption.
