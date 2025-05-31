void main() {
	int i = rand(1, 10);
	int j = rand(-10, -1);
	int k = rand(-10, -1);

	assert(i / j < 0); // @OK
	assert(j / i < 0); // @OK
	assert(j / k > 0); // @OK
}
