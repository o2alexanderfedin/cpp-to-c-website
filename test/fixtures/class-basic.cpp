// Basic class with members and methods
class Point {
private:
    int x;
    int y;

public:
    Point(int x_val, int y_val) : x(x_val), y(y_val) {}

    int getX() const {
        return x;
    }

    int getY() const {
        return y;
    }

    void setX(int new_x) {
        x = new_x;
    }

    void setY(int new_y) {
        y = new_y;
    }

    int distanceSquared() const {
        return x * x + y * y;
    }
};
