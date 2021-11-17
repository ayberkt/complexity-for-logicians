all: html/PRF.html

html/PRF.html: html/PRF.md
	pandoc -s --css=Agda.css -o $@ $<

html/PRF.md: PRF.lagda.md
	agda -v 0 --safe --html --html-highlight=auto $<
	cp Agda.css html/Agda.css

deploy:
	rsync -av html/* axt978@tinky-winky.cs.bham.ac.uk:public_html/complexity-for-logicians/

.PHONY: clean
clean:
	rm -rf html
