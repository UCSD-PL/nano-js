

all: TSC

TSC: typescript/src/compiler/tsc.ts 
	tsc typescript/src/compiler/tsc.ts  -out bin/tsc.js

#XMLG: src/xml_generator.ts
#	tsc src/xml_generator.ts -out bin/xmlG.js

clean:
	ls bin/*.js|grep -v tsc.js|xargs rm -rf

clean-all:
	find . -name "*.js" -exec rm -f {} \;
