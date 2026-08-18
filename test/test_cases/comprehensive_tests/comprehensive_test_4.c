
int add(int p1, int p2) {
    return p1 + p2;
}
int subtract(int p1, int p2) {
    return p1 - p2;
}
int is_even(int num) {
    return num % 2 == 0;
}
int is_odd(int num) {
    return num % 2 != 0;
}
int main() {
    int a = 10;
    int b = 5;
    int result = 0;
    if (is_even(add(a, b)) || is_odd(subtract(a, b))) {
        result = 1;
    } else {
        result = 0;
    }
    return result;
}


