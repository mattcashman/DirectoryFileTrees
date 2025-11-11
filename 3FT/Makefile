#--------------------------------------------------------------------
# Makefile for Assignment 4, Part 3
# Author: Alex Perkins & Matt Cashman
#--------------------------------------------------------------------

all: ft

clean:
	rm -f meminfo*.out

clobber: clean
	rm -f dynarray.o path.o ft_client.o 

ft: dynarray.o path.o nodeFT.o ft.o ft_client.o
	gcc217 ft.o ft_client.o -o ft 

dynarray.o: dynarray.c dynarray.h
	gcc217 -g -c $<

path.o: path.c dynarray.h path.h a4def.h
	gcc217 -g -c $<

ft_client.o: ft_client.c ft.h a4def.h
	gcc217 -g -c $<

nodeFT.o: nodeDTGood.c dynarray.h nodeFT.h path.h a4def.h
	gcc217 -g -c $<

ft.o: ft.c dynarray.h nodeFT.h dt.h path.h a4def.h
	gcc217 -g -c $<



