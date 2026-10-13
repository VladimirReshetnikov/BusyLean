# PDF quality-assurance report

- File: `article/contender20.pdf`
- SHA-256: `591dc056e00e6a486b8fe8c61d490fc11f1280d70f0844a165784b75eac93501`
- Size: 511951 bytes
- Page count: 30
- Page geometry: US Letter, 612 x 792 points
- Compilation: `latexmk -pdf -interaction=nonstopmode -halt-on-error`
- LaTeX diagnostics: no overfull boxes, underfull boxes, unresolved references,
  or unresolved citations in the final log
- Preflight: openable, unencrypted, non-scanned, no XFA
- Visual QA: all 30 pages rendered at 180 dpi and inspected in three contact
  sheets; full-size inspection was also performed on the architecture page,
  the source-listing transition, and the audit/checklist page
- Result: PASS; no clipping, overlap, black boxes, broken glyphs, or blank pages
  observed

The rendered PNGs were used only for QA and are intentionally not included in
the deliverable archive.
