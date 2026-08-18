int main() {
    int a = 1;
    int b = 2;
    if (a == 0) {
        b = 10; // Dead code
    }
    a = 3; // Live code
    if (b == 0) {
        a = 5; // Dead code
    }
    return a + b;
}


