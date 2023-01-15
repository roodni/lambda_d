# usage: make run P=検査する定義の名前

deflang := _build/default/bin/exdef.exe
automake := ./test_automake3
main := _build/default/bin/main.exe

deffile := inputs/mydef.txt
logfile := inputs/log.txt
outfile := inputs/out.txt

P := USE_ARG_P


.PHONY: run2
run2:
	_build/default/bin/script.exe inputs/exdef.txt > $(logfile)
	$(main) $(logfile) > $(outfile)


.PHONY: run
run: $(deffile)
	$(automake) $(deffile) $(P) $(logfile)
	$(main) $(logfile) > $(outfile)

$(deffile): inputs/exdef.txt $(deflang)
	$(deflang) inputs/exdef.txt > $(deffile)

.PHONY: clean
clean:
	-rm $(deffile) $(logfile) $(outfile)