SHELL := /bin/bash
.DELETE_ON_ERROR:

DATE=`date +%Y%m%d`

# for printing variable values
# usage: make print-VARIABLE
#        > VARIABLE = value_of_variable
print-%  : ; @echo $* = $($*)

# literal space
space :=
space +=

# Decide OS-specific questions
# jar-file seperator
ifeq ($(OS),Windows_NT)
	SEP = ;
else
# linux
	UNAME = $(shell uname)
	ifeq ($(UNAME),Darwin)
		SEP = :
	endif
	ifeq ($(UNAME),Linux)
		SEP = :
	endif
endif

# Fun Args to javac.  Mostly limit to java8 source definitions, and fairly
# agressive lint warnings.
JAVAC_ARGS = -g -source 1.8 -target 1.8 -XDignore.symbol.file -Xlint:all -Xlint:-deprecation -Xlint:-serial -Xlint:-rawtypes -Xlint:-unchecked

# Source code
# Note that BuildVersion is not forced to be rebuilt here - so incremental
# makes in this directory will endlessly use the same BuildVersion.
AA  := com/cliffc/aa
SRC := src/main/java
TST := src/test/java
CLZDIR:= build/classes
main_javas   := $(wildcard $(SRC)/$(AA)/*java $(SRC)/$(AA)/*/*java)
test_javas   := $(wildcard $(TST)/$(AA)/*java $(TST)/$(AA)/*/*java)
main_classes := $(patsubst $(SRC)/%java,$(CLZDIR)/main/%class,$(main_javas))
test_classes := $(patsubst $(TST)/%java,$(CLZDIR)/test/%class,$(test_javas))
classes = $(main_classes) $(test_classes)
javas = $(main_javas)
# All the libraries: see lib/README.md for more info
libs = $(wildcard lib/*jar)
jars = $(subst $(space),$(SEP),$(libs))

# Just build the AA jar file
default: build/aa.jar

# Just the classes, no jarring step
classes: $(classes)

# Build the test classes
test:	$(test_classes)

# Compile just the out-of-date files
$(main_classes): build/classes/main/%class: $(SRC)/%java
	@echo "compiling " $@ " because " $?
	@[ -d $(CLZDIR)/main ] || mkdir -p $(CLZDIR)/main
	@javac $(JAVAC_ARGS) -cp "$(CLZDIR)/main$(SEP)$(jars)" -sourcepath $(SRC) -d $(CLZDIR)/main $(javas)

$(test_classes): $(CLZDIR)/test/%class: $(TST)/%java $(main_classes)
	@echo "compiling " $@ " because " $?
	@[ -d $(CLZDIR)/test ] || mkdir -p $(CLZDIR)/test
	@javac $(JAVAC_ARGS) -cp "$(CLZDIR)/test$(SEP)$(CLZDIR)/main$(SEP)$(jars)" -sourcepath $(TST) -d $(CLZDIR)/test $(test_javas)

# Note the tabs - not spaces - in the grep and cut commands
PROJECT_VERSION=99999
BUILD_BRANCH=  git branch | grep '*' | sed 's/* //'
BUILD_HASH=    git log -1 --format="%H"
BUILD_DESCRIBE=git describe --always --dirty
BUILD_ON=      (TZ=UCT date)
BUILD_BY=      (whoami | cut -d\\ -f2-)

# Build the version file anytime anything would trigger the build/aa.jar
# i.e., identical dependencies to aa.jar, except aa.jar also includes the build file
$(CLZDIR)/main/$(AA)/BuildVersion.class: $(main_classes) src/main/manifest.txt
	@echo "vrsioning " $@ " because " $?
	@rm -f build/BuildVersion.java
	@mkdir -p $(dir $@)
	@echo "package com.cliffc.aa;"                                                        >  build/BuildVersion.java
	@echo "public class BuildVersion extends AbstractBuildVersion {"                      >> build/BuildVersion.java
	@echo "    public String branchName()     { return \"$(shell $(BUILD_BRANCH))\"; }"   >> build/BuildVersion.java
	@echo "    public String lastCommitHash() { return \"$(shell $(BUILD_HASH))\"; }"     >> build/BuildVersion.java
	@echo "    public String describe()       { return \"$(shell $(BUILD_DESCRIBE))\"; }" >> build/BuildVersion.java
	@echo "    public String projectVersion() { return \"$(PROJECT_VERSION)\"; }"         >> build/BuildVersion.java
	@echo "    public String compiledOn()     { return \"$(shell $(BUILD_ON))\"; }"       >> build/BuildVersion.java
	@echo "    public String compiledBy()     { return \"$(shell $(BUILD_BY))\"; }"       >> build/BuildVersion.java
	@echo "}"                                                                             >> build/BuildVersion.java
	@javac $(JAVAC_ARGS) -cp "$(CLZDIR)/main$(SEP)$(jars)" -sourcepath $(SRC) -d $(CLZDIR)/main build/BuildVersion.java
	@rm -f build/BuildVersion.java

# Other Resources in aa.jar:
JARBITS =
JARBITS += -C $(CLZDIR)/main .    # The java class files

build/aa.jar: $(main_classes) $(test_classes) $(CLZDIR)/main/$(AA)/BuildVersion.class src/main/manifest.txt
	@echo "  jarring " $@ " because " $?
	@[ -d build ] || mkdir -p build
# Build the aa.jar file.  All included jars are unpacked into a flat
# structure, then repacked into One Jar Name collisions amongst packages are
# quietly ignored.  aa names win over all other names.
	@jar -cfm build/aa.jar src/main/manifest.txt $(JARBITS)

# find all java in the src/test directory
# Cut the "./water/MRThrow.java" down to "water/MRThrow.java"
# Cut the   "water/MRThrow.java" down to "water/MRThrow"
# Slash/dot "water/MRThrow"      becomes "water.MRThrow"
# add 'sort' to get determinism on order of tests on different machines
# methods within a class can still reorder due to junit?
# '/usr/bin/sort' needed to avoid windows native sort when run in cygwin
# Build the AA-test jar and run the junit tests
sandbox/tests.txt:	$(test_classes)
	@echo "  finding " $@ " because " $?
	@[ -d sandbox ] || mkdir -p sandbox
	@(cd ${TST}; /usr/bin/find . -name '*.java' | cut -c3- | sed "s/.....$$//" | sed -e 's/\//./g') | grep -v TestUtil | /usr/bin/sort > sandbox/tests.txt

# Base launch line for JVM tests
JVM=nice java -Xms1g -Xms1g -XX:+PrintGC -ea -cp "build/aa.jar${SEP}${jars}${SEP}$(CLZDIR)/test"

# Actually makes jvm_cmd.txt and status.0 along with out.0
sandbox/out.0:	sandbox/tests.txt $(test_classes) build/aa.jar 
	@echo "  testing " $@ " because " $?
	@echo $(JVM) > sandbox/jvm_cmd.txt
	@($(JVM) org.junit.runner.JUnitCore `cat sandbox/tests.txt`  2>&1 ; echo $$? > sandbox/status.0) 1> sandbox/out.0 2>&1

# Filter and sort test execution times
sandbox/timing.txt:	sandbox/out.0
	@grep EXECUTION $? | cut -d: -f5-8 | awk '{print $$6 " " $$3}' | /usr/bin/sort -gr > sandbox/timing.txt

# Report top n test times (for optimizing), and pass/fail on them all
check:	sandbox/timing.txt sandbox/out.0
	@head sandbox/timing.txt
	@tail -n 4 sandbox/out.0
	@[ `cat sandbox/status.0` -eq 0 ]

.PHONY: clean
clean:
	rm -rf build
	rm -rf out
	rm -f TAGS
	(find . -name "*~" -exec rm {} \; 2>/dev/null; exit 0)

# Called "conf" here, after auto-conf, but really just asks each sub-make to list tools
.PHONY: conf
conf:
	@echo $(CURDIR) requires java, jar
	java -version
	which jar

# Build emacs tags (part of a tasty emacs ide experience)
tags:	$(main_javas) $(test_javas)
	@rm -f TAGS
	@ctags -e --recurse=yes --extra=+q --fields=+fksaiS $(SRC) $(TST)
