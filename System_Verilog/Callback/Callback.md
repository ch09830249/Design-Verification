1. Callbacks are designed to be dynamically registered and invoked during runtime.  
    This means you can change the behavior of your system without modifying the original code.  
2. A callback is usually registered by one part of the code and then called by another part.  
    The calling part doesn’t need to know what the callback will do  
3. Callbacks promote loose coupling between components.  
   
Empty tasks can be positioned at key points within the code, allowing new code to be added to those spots later on.
![image](https://github.com/user-attachments/assets/f37d3ae9-d5f9-46d6-b76e-df992ad1edf8)

For example, pre_err_callback and post_err_callback are two empty methods defined in base test  
which are then overridden in a child class to implement some functionality to executed before and after error injection.  
So, these two methods were just placeholders in the base code to allow it to be enhanced or modified to some extent without touching the base class.
```
class MyTest;
 ...

  virtual task body();
     // some statements
     pre_err_callback();
     err_inj_seq();
     post_err_callback();
     // more statements
  endtask

  virtual task pre_err_callback();
    // Empty callback
  endtask

  virtual task post_err_callback();
    // Empty callback
  endtask
endclass

class MyTestExt extends MyTest;

  virtual task pre_err_callback();
    // Implement things to be done before error injection
  endtask

  virtual task post_err_callback();
    // Implement things to be done after error injection
  endtask
endclass
```
