# Só um makefile para fazer o relatório
relatorio.pdf: relatorio.tex
	pdftex $^

relatorio.tex: app/cp2021t.lhs
	lhs2TeX $^ > $@
