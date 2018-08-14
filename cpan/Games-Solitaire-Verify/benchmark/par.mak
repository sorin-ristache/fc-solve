# perl -E 'print "INDEXES ="; print " ", $_*100+1 for 0 .. 319; print "\n"'
INDEXES = 1 101 201 301 401 501 601 701 801 901 1001 1101 1201 1301 1401 1501 1601 1701 1801 1901 2001 2101 2201 2301 2401 2501 2601 2701 2801 2901 3001 3101 3201 3301 3401 3501 3601 3701 3801 3901 4001 4101 4201 4301 4401 4501 4601 4701 4801 4901 5001 5101 5201 5301 5401 5501 5601 5701 5801 5901 6001 6101 6201 6301 6401 6501 6601 6701 6801 6901 7001 7101 7201 7301 7401 7501 7601 7701 7801 7901 8001 8101 8201 8301 8401 8501 8601 8701 8801 8901 9001 9101 9201 9301 9401 9501 9601 9701 9801 9901 10001 10101 10201 10301 10401 10501 10601 10701 10801 10901 11001 11101 11201 11301 11401 11501 11601 11701 11801 11901 12001 12101 12201 12301 12401 12501 12601 12701 12801 12901 13001 13101 13201 13301 13401 13501 13601 13701 13801 13901 14001 14101 14201 14301 14401 14501 14601 14701 14801 14901 15001 15101 15201 15301 15401 15501 15601 15701 15801 15901 16001 16101 16201 16301 16401 16501 16601 16701 16801 16901 17001 17101 17201 17301 17401 17501 17601 17701 17801 17901 18001 18101 18201 18301 18401 18501 18601 18701 18801 18901 19001 19101 19201 19301 19401 19501 19601 19701 19801 19901 20001 20101 20201 20301 20401 20501 20601 20701 20801 20901 21001 21101 21201 21301 21401 21501 21601 21701 21801 21901 22001 22101 22201 22301 22401 22501 22601 22701 22801 22901 23001 23101 23201 23301 23401 23501 23601 23701 23801 23901 24001 24101 24201 24301 24401 24501 24601 24701 24801 24901 25001 25101 25201 25301 25401 25501 25601 25701 25801 25901 26001 26101 26201 26301 26401 26501 26601 26701 26801 26901 27001 27101 27201 27301 27401 27501 27601 27701 27801 27901 28001 28101 28201 28301 28401 28501 28601 28701 28801 28901 29001 29101 29201 29301 29401 29501 29601 29701 29801 29901 30001 30101 30201 30301 30401 30501 30601 30701 30801 30901 31001 31101 31201 31301 31401 31501 31601 31701 31801 31901

RESULTS = $(patsubst %,Results/%.res,$(INDEXES))

all: $(RESULTS)

$(RESULTS): %:
	i="$(patsubst Results/%.res,%,$@)"; F="$$i" L="$$((i + 99))" perl -I. benchmark-no-backticks.pl -- -l cm -ni -l fg > $@

cat: $(RESULTS)
	cat $(RESULTS)

