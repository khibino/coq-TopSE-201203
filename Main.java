import java.util.*;

public class Main {
    public static void main(String[] args) {
        System.out.println(Wrapper.coq_reverse(args));
    }
}

class Wrapper {
    static <A> CoqMain.List<Object> toCoqList(A[] xs) {
        CoqMain.List<Object> ys = new CoqMain.Nil<Object>();
        for (int i = xs.length - 1; i >= 0; i--) {
            ys = new CoqMain.Cons<Object>(xs[i], ys);
        }
        return ys;
    }

    static ArrayList<Object> ofCoqList(CoqMain.List<Object> xs) {
        ArrayList<Object> ys = new ArrayList<Object>();
        while(xs instanceof CoqMain.Cons) {
            ys.add(((CoqMain.Cons)xs).x1());
            xs = ((CoqMain.Cons<Object>)xs).x2();
        }
        return ys;
    }

    static <A> ArrayList coq_reverse(A[] xs) {
        return ofCoqList(CoqMain$.MODULE$.rev().apply(toCoqList(xs)));
    }
}