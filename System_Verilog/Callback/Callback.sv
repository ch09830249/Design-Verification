/*
    Callback: A callback lets you give a function to someone else’s program. 
            When that program reaches a certain point or condition, it "calls back" your function and runs it.

    
    Callback in SV: A class method is written to call placeholder methods.  建一個 class, 裡面的建一個 Virtual function 當作 placeholder
                    When needed, the user can extend the class and implement these placeholder methods. 
                    Here, the placeholder methods are the callback methods, and the calls to these methods act as callback hooks.

*/



/*
    1. Callback Class: The callback functionality is usually implemented in a class where certain methods are defined. 
                       These methods can be overridden or extended by other classes.   
                       創一個 placeholder (運用父類 handle 可以指向一個子類 handle 的特性, 後續實作的子類, 都可以用父類的 handle 去接)
*/

class MyCallback;                                 // 可以看作是一個 prototype
  virtual function void callback_function();      // 這裡要是用 virtual 的用意是, 到時候呼叫該 func 會強制呼叫子類的 func, 而非父類的
    // Default implementation (optional)
  endfunction
endclass

/*
    2. Registration of Callbacks: To use callbacks, the class containing the method must register 
                                  the callback object with the system. 
                                  This allows the system to store a reference to the method that will be called later.
*/

class MyTest;
  MyCallback cb;    // 相較 C 用 func ptr 傳入 func, 這裡是傳入繼承 MyCallback 的子類 handle, 這個 handle 會去接子類的 object
  // 2. Registration of callback
  function void register_callback(MyCallback callback); // 在 class MyTest 透過 MyCallback 的 handle 接它的子類物件
    cb = callback;
  endfunction

  function void execute();  // 在看何時透過該 MyCallback 的 handle 去呼叫 callback function (正因為父類 func 為 virtual, 所以用 MyCallback 的 handle 會呼叫到子類的該方法)
    if (cb != null) begin
      cb.callback_function();
    end
  endfunction
endclass

/*
    3. Implementation of Callbacks: The functionality that has to be executed when invoking the callback 
    has to be implemented in a child class.
*/

// 3. Callback implementation
class UserCallback extends MyCallback;      // 這裡就是繼承 MyCallback 的子類去實作 callback func, 每個子 class 有不同的實作
  function void callback_function();
    $display("User-defined callback called!");
  endfunction
endclass

/*
    4. Invoking the Callback: When an event or condition occurs in the simulation, 
    the callback is invoked by calling the registered methods. 
    The invoking class doesn’t know the details of what the callback will do, allowing for flexible behavior.
*/
module tb;

  initial begin
    MyTest        test;
    UserCallback  user_cb;            // Callback function 可以根據需求有不同實作

    test    = new;
    user_cb = new;

    // Register user-defined callback
    test.register_callback(user_cb);

    // 4. Execute which will invoke the callback
    test.execute();
  end
endmodule

/*
    User-defined callback called!
*/

/*
    MyCallback class defines a virtual function callback_function().    
        Virtual func 就是一個 func 的 placeholder 但是不實作
    MyTest class has a function to register a callback and later executes the callback function when needed.    
    UserCallback extends MyCallback and overrides the callback_function() method.
    The testbench registers the UserCallback object and calls execute(), which invokes the registered callback function.
*/