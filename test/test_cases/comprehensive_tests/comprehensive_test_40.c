
int add(int p1, int p2) {
    return p1 + p2;
}
int subtract(int p1, int p2) {
    return p1 - p2;
}
int get_five() {
    return 5;
}
int is_even(int num) {
    return num % 2 == 0;
}
int main() {
    int i = 0;
    int sum = 0;
    while (i < 20) {
        if (is_even(i)) {
            sum = sum + add(i, get_five());
        } else {
            sum = sum + subtract(i, get_five());
        }
        if (sum > 100) {
            break;
        }
        i = i + 1;
    }
    return sum;
}


