#include <stdlib.h>
#include <alloca.h>

struct p {
	struct p * next;
	int data;
};

struct p * f(struct p *ptr) {
	struct p *ret = ptr->next;
	free(ptr); // len(ptr) >= next
	return ret;
}

int main() {
	struct p *elm = malloc(sizeof(struct p)); // len(elm) = next+data
	elm = f(elm);
	return 0;
}
