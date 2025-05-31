void main () {
	int i = rand(1, 2);
	int j = i * 2;
	if (j >= 3) {
		assert(i > 1); //@OK
	}
}
