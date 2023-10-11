.PHONY: check html clean

check:
	pymarkdown scan README.md

html: README.html

clean:
	rm -f README.html *~

README.html: README.md
	pandoc -s -f markdown -t html -o $@ $<
