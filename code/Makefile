CC = gcc
CXX = g++
LIBS = -lrt
CFLAGS = --std=c++11 -W -Wall -Wno-sign-compare -O3 -s -pipe -mmmx -msse -msse2 -msse3 -mcmodel=large
TARGET = ./all

all: PCSP LSD Dijkstra
PCSP: Regex2MinDFA.h PCSP.cpp
	$(CXX) $(CFLAGS) -o PCSP Regex2MinDFA.h PCSP.cpp

LSD: LSD.cpp
	$(CXX) $(CFLAGS) -o LSD LSD.cpp
	
Dijkstra: Regex2MinDFA.h Dijkstra.cpp
	$(CXX) $(CFLAGS) -o Dijkstra Regex2MinDFA.h Dijkstra.cpp

.PHONY: clean
clean:
		-@rm *.o *.gcno *~ 2> /dev/null || true
		-@rm SOR shortestPath SRH Statistic 2> /dev/null || true
