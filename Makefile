CXXFLAGS=-std=c++11 -Wall -O3 -march=native -fwhole-program
LDFLAGS=-flto -lgmp -lgmpxx

A273525: A273525.cpp
	g++ A273525.cpp -o A273525 $(CXXFLAGS) $(LDFLAGS)

clean:
	rm A273525

.PHONY: clean
