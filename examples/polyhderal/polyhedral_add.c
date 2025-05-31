void main() {
	int i = rand(1, 10);
	int j = i - 5;
	int k = rand(5, 10);
	assert(j + k >= i); //@OK
}
