int get_value(int num) {
    return num * 10;
}
int main() {
    int i = 0;
    int sum = 0;
    while (i < 5) {
        sum = sum + get_value(i);
        i = i + 1;
    }
    return sum;
}


