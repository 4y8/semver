void main() {
	int i = rand(1, 10);
	int j = rand(0, 10);
	
	assert(i + j > 0); // @OK
}
