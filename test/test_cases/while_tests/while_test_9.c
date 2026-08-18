int main() {
    int i = 0;
    int sum = 0;
    while (1) {
        sum = sum + i;
        i = i + 1;
        if (i > 10) {
            break;
        }
    }
    return sum;
}


