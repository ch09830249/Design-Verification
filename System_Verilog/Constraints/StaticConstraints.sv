/*
    A static constraint is shared across all the class instances.
    Constraints are affected by the static keyword only if they are turned on and off using constraint_mode() method. 
    When a non-static constraint is turned off using this method, 
    the constraint is turned off in that particular instance of the class which calls the method. 
    But, when a static constraint is turned off and on using this method, 
    the constraint is turned off and on in all the instances of the class.

    A constraint block can be declared as static by including the static keyword in its definition.

    Syntax
        class [class_name];
            ...

            static constraint [constraint_name] [definition]
        endclass
*/


// Non-static Constraints       每個 instance 各自保有自己的 constraints
class ABC;
  rand bit [3:0]  a;

  // Both are non-static constraints
  constraint c1 { a > 5; }
  constraint c2 { a < 12; }
endclass

module tb;
  initial begin
    ABC obj1 = new;
    ABC obj2 = new;
    for (int i = 0; i < 5; i++) begin
      obj1.randomize();
      obj2.randomize();
      $display ("obj1.a = %0d, obj2.a = %0d", obj1.a, obj2.a);
    end
  end
endmodule

/*
    obj1.a = 9, obj2.a = 6
    obj1.a = 7, obj2.a = 11
    obj1.a = 6, obj2.a = 6
    obj1.a = 9, obj2.a = 11
    obj1.a = 6, obj2.a = 9
*/


// Static Constraints   一個 class 共享一個 constraints
class ABC;
  rand bit [3:0]  a;

  // "c1" is non-static, but "c2" is static
  constraint c1 { a > 5; }
  static constraint c2 { a < 12; }          // 在 Constraint 前面加關鍵字 static, 和一般 static 變數一樣
endclass

module tb;
  initial begin
    ABC obj1 = new;
    ABC obj2 = new;

    // Turn off non-static constraint
    obj1.c1.constraint_mode(0);         // 透過 obj1 instance 關掉此 class 的 c1 constraints

    for (int i = 0; i < 5; i++) begin
      obj1.randomize();
      obj2.randomize();
      $display ("obj1.a = %0d, obj2.a = %0d", obj1.a, obj2.a);
    end
  end
endmodule

/*
    obj1.a = 3, obj2.a = 6          這裡 obj2 不受影響是因為 c1 為 non-static constraints
    obj1.a = 7, obj2.a = 11
    obj1.a = 6, obj2.a = 6
    obj1.a = 9, obj2.a = 11
    obj1.a = 6, obj2.a = 9
*/

class ABC;
  rand bit [3:0]  a;

  // "c1" is non-static, but "c2" is static
  constraint c1 { a > 5; }
  static constraint c2 { a < 12; }
endclass

module tb;
  initial begin
    ABC obj1 = new;
    ABC obj2 = new;

    // Turn non-static constraint
    obj1.c2.constraint_mode(0);         // 透過 obj1 關掉 c2 constraints

    for (int i = 0; i < 5; i++) begin
      obj1.randomize();
      obj2.randomize();
      $display ("obj1.a = %0d, obj2.a = %0d", obj1.a, obj2.a);
    end
  end
endmodule

/*
    obj1.a = 15, obj2.a = 12        // 兩個 obj 皆不再遵守 c2 constraints
    obj1.a = 9, obj2.a = 15
    obj1.a = 14, obj2.a = 6
    obj1.a = 11, obj2.a = 11
    obj1.a = 12, obj2.a = 11
*/