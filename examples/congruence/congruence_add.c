void main() {
	int i = rand(1, 5);
	int j = rand(1, 5);
	if (i % 2 == 0 && j % 2 == 0) {
		assert(i + j % 2 != 1); // @OK
	} 
}
