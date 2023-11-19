SHELL := /bin/bash
.DELETE_ON_ERROR:

DATE=`date +%Y%m%d`

# for printing variable values
# usage: make print-VARIABLE
#        > VARIABLE = value_of_variable
print-%  : ; @echo $* = $($*)

# literal space
space := $() $()

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
# Find a reasonable ctags.
CTAGS = $(shell which ctags)
# Hack for MacOS: /usr/bin/ctags is unfriendly, so look for ctags from brew
ifeq ($(UNAME),Darwin)
	CTAGS = $(shell brew list ctags 2> /dev/null | grep bin/ctags)
endif

# Fun Args to javac.  Mostly limit to java8 source definitions, and fairly
# aggressive lint warnings.
JAVAC_ARGS = -g -XDignore.symbol.file -Xlint:-deprecation

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
# All the libraries: see lib/README.md for more info
libs = $(wildcard lib/*jar)
jars = $(subst $(space),$(SEP),$(libs))


default_targets := build/aa.jar
# Optionally add ctags to the default target if a reasonable one was found.
ifneq ($(CTAGS),)
default_targets += tags
endif

default: $(default_targets)

# Just the classes, no jarring step
classes: $(classes)

# Build the test classes
test:	$(test_classes)

# Compile just the out-of-date files
$(main_classes): build/classes/main/%class: $(SRC)/%java
	@echo "compiling " $@ " because " $?
	@[ -d $(CLZDIR)/main ] || mkdir -p $(CLZDIR)/main
	@javac $(JAVAC_ARGS) -cp "$(CLZDIR)/main$(SEP)$(jars)" -sourcepath $(SRC) -d $(CLZDIR)/main $(main_javas)

$(test_classes): $(CLZDIR)/test/%class: $(TST)/%java $(main_classes)
	@echo "compiling " $@ " because " $?
	@[ -d $(CLZDIR)/test ] || mkdir -p $(CLZDIR)/test
	@javac $(JAVAC_ARGS) -cp "$(CLZDIR)/test$(SEP)$(CLZDIR)/main$(SEP)$(jars)" -sourcepath $(TST) -d $(CLZDIR)/test $(test_javas)

# Note the tabs - not spaces - in the grep and cut commands
PROJECT_VERSION=0.0.1
BUILD_BRANCH=  git branch | grep '*' | sed 's/* //'
BUILD_HASH=    git log -1 --format="%H"
BUILD_DESCRIBE=git describe --always --dirty
BUILD_ON=      (TZ=UCT date)
BUILD_BY=      (whoami | cut -d\\ -f2-)

# Build the version file anytime anything would trigger the build/aa.jar.
# i.e., identical dependencies to aa.jar, except aa.jar also includes the test
# files and the BuildVersion file.
$(CLZDIR)/main/$(AA)/BuildVersion.java: $(main_classes) src/main/manifest.txt lib
	@echo "vrsioning " $@ " because " $?
	@rm -f $@
	@mkdir -p $(dir $@)
	@echo "package com.cliffc.aa;"                                                        >  $@
	@echo "public class BuildVersion extends AbstractBuildVersion {"                      >> $@
	@echo "    public String branchName()     { return \"$(shell $(BUILD_BRANCH))\"; }"   >> $@
	@echo "    public String lastCommitHash() { return \"$(shell $(BUILD_HASH))\"; }"     >> $@
	@echo "    public String describe()       { return \"$(shell $(BUILD_DESCRIBE))\"; }" >> $@
	@echo "    public String projectVersion() { return \"$(PROJECT_VERSION)\"; }"         >> $@
	@echo "    public String compiledOn()     { return \"$(shell $(BUILD_ON))\"; }"       >> $@
	@echo "    public String compiledBy()     { return \"$(shell $(BUILD_BY))\"; }"       >> $@
	@echo "}"                                                                             >> $@

$(CLZDIR)/main/$(AA)/BuildVersion.class: $(CLZDIR)/main/$(AA)/BuildVersion.java
	@javac $(JAVAC_ARGS) -cp "$(CLZDIR)/main$(SEP)$(jars)" -sourcepath $(SRC) -d $(CLZDIR)/main $(CLZDIR)/main/$(AA)/BuildVersion.java

# Other Resources in aa.jar:
JARBITS =
JARBITS += -C $(CLZDIR)/main .    # The java class files

build/aa.jar: $(main_classes) $(test_classes) $(CLZDIR)/main/$(AA)/BuildVersion.class src/main/manifest.txt lib
	@echo "  jarring " $@ " because " $?
	@[ -d build ] || mkdir -p build
# Build the aa.jar file.  All included jars are unpacked into a flat structure,
# then repacked into One Jar.  Name collisions amongst packages are quietly
# ignored.  aa names win over all other names.
	@jar -cfm build/aa.jar src/main/manifest.txt $(JARBITS)

# find all java in the src/test directory
# Cut the "./water/MRThrow.java" down to "water/MRThrow.java"
# Cut the   "water/MRThrow.java" down to "water/MRThrow"
# Slash/dot "water/MRThrow"      becomes "water.MRThrow"
# add 'sort' to get determinism on order of tests on different machines.
# '/usr/bin/sort' needed to avoid windows native sort when run in cygwin.
sandbox/tests.txt:	$(test_classes)
	@echo "  finding " $@ " because " $?
	@[ -d sandbox ] || mkdir -p sandbox
	@(cd ${TST}; /usr/bin/find . -name '*.java' | cut -c3- | sed "s/.....$$//" | sed -e 's/\//./g') | grep -v TestUtil | /usr/bin/sort > sandbox/tests.txt

# Base launch line for JVM tests
JVM=nice java -Xms1g -Xms1g -XX:+PrintGC -ea -cp "build/aa.jar${SEP}${jars}${SEP}$(CLZDIR)/test"

# Build the AA-test jar and run the junit tests.
# Actually makes jvm_cmd.txt and status.0 along with out.0
sandbox/out.0:	sandbox/tests.txt $(test_classes) build/aa.jar 
	@echo "  testing " $@ " because " $?
	@echo $(JVM) org.junit.runner.JUnitCore `cat sandbox/tests.txt` > sandbox/jvm_cmd.txt
	@($(JVM) org.junit.runner.JUnitCore `cat sandbox/tests.txt`  2>&1 ; echo $$? > sandbox/status.0) 1> sandbox/out.0 2>&1

# Filter and sort test execution times
sandbox/timing.txt:	sandbox/out.0
	@grep EXECUTION $? | cut -d: -f5-8 | awk '{print $$6 " " $$3}' | /usr/bin/sort -gr > sandbox/timing.txt

# Report top n test times (for optimizing), and pass/fail on them all
check:	sandbox/timing.txt sandbox/out.0
	@head sandbox/timing.txt
	@tail -n 4 sandbox/out.0
	@[ `cat sandbox/status.0` -eq 0 ]

hm_tests:	$(test_classes) build/aa.jar
	$(JVM) org.junit.runner.JUnitCore com.cliffc.aa.HM.TestHM


# EXE, a standalone lambda calc interpreter
exec_javas   := $(wildcard $(SRC)/$(AA)/exe/*java)
etst_javas   := $(wildcard $(TST)/$(AA)/exe/*java)
exec_classes := $(patsubst $(SRC)/%java,$(CLZDIR)/main/%class,$(exec_javas))
etst_classes := $(patsubst $(TST)/%java,$(CLZDIR)/test/%class,$(etst_javas))

%.exe : %.aa $(main_classes) $(exec_classes)
	@echo Running $<
	@java -Xms1g -Xms1g -ea -cp "${CLZDIR}/main" com.cliffc.aa.exe.EXE $<


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

# Download libs from maven
lib:	lib/junit-4.12.jar lib/hamcrest-core-1.3.jar lib/system-rules-1.19.0.jar lib/annotations-16.0.2.jar

# Unit testing
lib/junit-4.12.jar lib/hamcrest-core-1.3.jar lib/system-rules-1.19.0.jar:
	@[ -d lib ] || mkdir -p lib
	@(cd lib; wget https://repo1.maven.org/maven2/junit/junit/4.12/junit-4.12.jar)
	@(cd lib; wget https://repo1.maven.org/maven2/org/hamcrest/hamcrest-core/1.3/hamcrest-core-1.3.jar)
	@(cd lib; wget https://repo1.maven.org/maven2/com/github/stefanbirkner/system-rules/1.19.0/system-rules-1.19.0.jar)

# @NotNull annotations
lib/annotations-16.0.2.jar:
	@[ -d lib ] || mkdir -p lib
	@(cd lib; wget https://repo1.maven.org/maven2/org/jetbrains/annotations/16.0.2/annotations-16.0.2.jar)

# Build emacs tags (part of a tasty emacs ide experience)
tags:	$(main_javas) $(test_javas) $(exec_javas)
	@rm -f TAGS
	@$(CTAGS) -e --recurse=yes --extra=+q --fields=+fksaiS $(SRC) $(TST)
