# usage: make run P=検査する定義の名前

deflang := _build/default/bin/defconv.exe
automake := _build/default/bin/automake.exe
# automake := ./test_automake3
main := _build/default/bin/main.exe
# main := ./test_book3

exdeffile := inputs/exdef.txt
deffile := inputs/mydef.txt
logfile := inputs/log.txt
outfile := inputs/out.txt

P := f11_29_a7


.PHONY: run
run: $(deffile)
	$(automake) $(deffile) $(P) $(logfile)
	$(main) $(deffile) $(logfile) > $(outfile)

$(deffile): $(exdeffile)
	$(deflang) $(exdeffile) > $(deffile)


.PHONY: run2
run2:
	_build/default/bin/script.exe $(exdeffile) > $(logfile)
	$(main) $(deffile) $(logfile) > $(outfile)


.PHONY: clean
clean:
	-rm $(deffile) $(logfile) $(outfile)