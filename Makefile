
README.html: README.md
	pandoc -s -f markdown -t html -o $@ $<
