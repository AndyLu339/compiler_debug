int main() {
    int temp = 25;
    int c = 0;
    if (temp < 0) {
        c = -1;
    } else if (temp < 10) {
        c = 0;
    } else if (temp < 20) {
        c = 1;
    } else if (temp < 30) {
        c = 2;
    } else {
        c = 3;
    }
    return c;
}


