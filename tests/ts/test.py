import os
import re
import sys

#Path to the binary that converts TS into XML.
PATH_TO_NANOTS = '../../../../nano-ts/run'
#Path to the binary that converts JS into Haskell data.
PATH_TO_HSCG   = './hscg'
#Path to the binary that converts XML into Haskell data.
PATH_TO_NANOJSPARSER = '../../../../nano-js/Language/TypeScript/Parse'
#Path to testfiles
PATH_TO_TESTS = './'


def generateXML(l):
    print l
    for fname in l:
        print PATH_TO_NANOTS+ ' '+fname+' > '+fname[:-2]+'xml'
        os.system(PATH_TO_NANOTS+ ' '+fname+' > '+fname[:-2]+'xml')

def cleanHSC(filename):
    f = open(filename,'r')
    str = re.sub('\(Span[^)]*\), sp_end[^)]*\)}\)', '()', f.read())
    f.close()
    f = open(filename,'w')
    f.write(str[7:-2]+'\n')
    f.close()

def generateHSCfromJS(l):
    print l
    for fname in l:
        print PATH_TO_HSCG+ ' '+fname+' > '+fname[:-3]+'.hsc'
        os.system(PATH_TO_HSCG+ ' '+fname+' > '+fname[:-3]+'.hsc')
        cleanHSC(fname[:-2]+'hsc')

def generateHSCfromXML(l):
    print l
    for fname in l:
        print PATH_TO_NANOJSPARSER+ ' '+fname+' > '+fname[:-4]+'.hscxml'
        os.system(PATH_TO_NANOJSPARSER+ ' '+fname+' > '+fname[:-4]+'.hscxml')

def differ():
    l = [ PATH_TO_TESTS+f for f in os.listdir(PATH_TO_TESTS) if os.path.isfile(PATH_TO_TESTS+f) and f[-4:] == '.hsc']
    print l
    for fname in l:
        print '##Diff for: '+fname+' vs '+fname[:-3]+'hscxml:'
        os.system('diff '+fname+' '+fname[:-3]+'hscxml')

def clean():
    l = [ PATH_TO_TESTS+f for f in os.listdir(PATH_TO_TESTS) if os.path.isfile(PATH_TO_TESTS+f) and (f[-4:] == '.hsc' or f[-4:] == '.xml' or f[-7:] == '.hscxml' or f[-3:] == '.js')]
    print l
    for fname in l:
        os.system('rm '+fname)

def main(l):
    global PATH_TO_TESTS
    global PATH_TO_NANOTS
    global PATH_TO_NANOJSPARSER
    global PATH_TO_HSCG 
    if '--help' in l:
        print "usage python test.py [--ts2hsc] [--ts2xml] [--xml2hsc] [--clean] [--differ] [-DGLOBALVAR=VALUE]"
        return;
    for i in l:
        if '-DPATH_TO_TESTS' in i:
            PATH_TO_TESTS = i.split('=')[1]
            PATH_TO_TESTS = PATH_TO_TESTS if (PATH_TO_TESTS[-1]=='/') else PATH_TO_TESTS+'/'
        if '-DPATH_TO_NANOTS' in i:
            PATH_TO_NANOTS = i.split('=')[1]
        if '-DPATH_TO_NANOJSPARSER' in i:
            PATH_TO_NANOJSPARSER = i.split('=')[1]
        if '-DPATH_TO_HSCG' in i:
            PATH_TO_HSCG = i.split('=')[1]
    tsfiles  = [ PATH_TO_TESTS+f for f in os.listdir(PATH_TO_TESTS) if os.path.isfile(PATH_TO_TESTS+f) and f[-3:] == '.ts']
    if '--ts2hsc' in l:
        generateHSCfromJS(tsfiles)
    if '--ts2xml' in l:
        generateXML(tsfiles)
    if '--xml2hsc' in l:
        xmlfiles = [ PATH_TO_TESTS+f for f in os.listdir(PATH_TO_TESTS) if os.path.isfile(PATH_TO_TESTS+f) and f[-4:] == '.xml']
        generateHSCfromXML(xmlfiles)
    if '--differ' in l:
        differ()
    if '--clean' in l:
        clean()


if __name__ == "__main__":
    main(sys.argv[1:])


        
    
