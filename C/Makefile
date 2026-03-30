CC = gcc
CFLAGS = -std=c11 -Wall -Wextra -g -Iinclude
SRCDIR = src
SRCS = sparse_client.c alloc.c sparse.c build_csr2.c 
OBJS = $(SRCS:.c=.o)

.PHONY: all clean

all: sparse_client

sparse_client: $(OBJS)
	$(CC) $(CFLAGS) -o $@ $(OBJS)

%.o: $(SRCDIR)/%.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) sparse_client