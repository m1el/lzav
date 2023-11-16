#include "lzav.h"
#include <stdio.h>

void hd(void* buf, size_t len) {
	unsigned char* bbuf = buf;
	for (size_t ii = 0; ii < len; ii+= 1) {
		if (ii && (ii & 0x1f) == 0) {
			printf("\n");
		}
		printf("%02x", bbuf[ii]);
	}
	printf("\n");
}

#define SRCL 1024
#define DSTL 2048
typedef unsigned char u8;
int main(int argc, char** argv) {
	u8 src[SRCL];
	u8 dst[2048];
	for(size_t ii = 0; ii < SRCL; ii += 1) {
		src[ii] = (u8)ii;
	}
	int result = lzav_compress((const void*)src, (void*) dst, SRCL, 2048, 0, 0);
	if (result < 0) {
		printf("big sad %d\n", result);
		return 1;
	}
	size_t len = (size_t)result;
	hd(dst, len);
}
