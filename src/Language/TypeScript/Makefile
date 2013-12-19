all: Parse.hs
	ghc -XFlexibleInstances Parse.hs 


test: all
	#ghc ./testfiles/hscg.hs
	python ./testfiles/test.py -DPATH_TO_NANOJSPARSER=../../../nano-js/Language/TypeScript/Parse -DPATH_TO_NANOTS=../../../nano-ts/run -DPATH_TO_HSCG=./testfiles/hscg -DPATH_TO_TESTS=./testfiles --ts2xml --xml2hsc

clean:
	python ./testfiles/test.py -DPATH_TO_TESTS=./testfiles --clean
	rm Parse.o Parse.hi

clean-all: 
	python ./testfiles/test.py -DPATH_TO_TESTS=./testfiles --clean
	rm Parse Parse.o Parse.hi ./testfiles/hscg ./testfiles/hscg.o ./testfiles/hscg.hi
