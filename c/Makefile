include Makefile.basic

%.o:%.c
	@echo "CC" $@
	@$(CC) $(CPPFLAGS) $(CFLAGS) -c -o $@ $<

test.exe:$(OBJS) test.o
	@echo "CC" $@
	@$(CC) $(CPPFLAGS) $(CFLAGS) -o $@ $^



