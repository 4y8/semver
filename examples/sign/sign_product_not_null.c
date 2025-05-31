void main () {
	int i = rand(1, 100);
	int j = rand(-100, -1);
	assert(i * j != 0); // @OK
}
