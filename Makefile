.PHONY: diff
diff:
	gcc -O2 test.c -o c_test && ./c_test > c_compressed
	rustc -O lzav.rs && ./lzav > rust_compressed
	diff c_compressed rust_compressed && echo same
