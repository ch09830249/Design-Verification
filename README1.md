## Strategy Pattern（策略模式）
* 是一種行為型設計模式 (一個類的行為或其演算法可以在運行時更改。這種類型的設計模式屬於行為型模式。)，它讓你可以定義一組演算法（策略），並且可以在執行期間動態地選擇其中一個來使用，而不需要將演算法寫死在使用者的程式碼中。
* 將**演算法的定義與其使用者解耦（分開）**，讓演算法可以**獨立變化、替換或擴展**，而不影響使用它的程式。
## 優點
1. 演算法切換自由：可以在運行時根據需要切換演算法。
2. 避免多重條件判斷：消除了複雜的條件語句。
3. 擴展性好：新增演算法只需新增一個策略類，無需修改現有代碼。
## 缺點
1. 策略類數量增多：每增加一個演算法，就需要增加一個策略類。
2. 所有策略類都需要暴露：策略類需要對外公開，以便可以被選擇和使用。
## 結構
* **環境（Context）**：維護一個對策略物件的引用，負責將用戶端請求委派給具體的策略對象執行。環境類可以通過依賴注入、簡單工廠等方式來獲取具體策略物件。**(使用策略的物件，不直接實作演算法。)**
* **抽象策略（Abstract Strategy）**：定義了策略物件的公共介面或抽象類，規定了具體策略類必須實現的方法。**(定義所有策略都應實作的共通方法。)**
* **具體策略（Concrete Strategy）**：實現了抽象策略定義的介面或抽象類，包含了具體的演算法實現。**(實際演算法實作，各自有不同行為。)**  
![image](https://github.com/user-attachments/assets/12fdc067-8f4d-44ce-9a00-14a6df195bd7)
![image](https://github.com/user-attachments/assets/b7f185f3-714e-4a3a-bf67-868fe624916c)
## Example1
* 先定義一個介面，用這個介面定義一系列演算法。
```
public interface IStrategy {
    public int caculate(int a , int b);
}
```
* 將加減乘除等一系列的算法實現出來
```
public class add implements IStrategy {
    @Override
    public int caculate(int a, int b) {
        return a + b;
    }
}

public class minus implements IStrategy {
    @Override
    public int caculate(int a, int b) {
        return a - b ;
    }
}

public class multyply implements IStrategy {
    @Override
    public int caculate(int a, int b) {
        return a * b;
    }
}

public class divide implements IStrategy {
    @Override
    public int caculate(int a, int b) {
        return a / b ;
    }
}
```
* 用一個類裝這個算法，並且用簡單的工廠模式封裝一下 (下一個例子會用 setter 設定 strategy)
```
public class Calculator {

    private int now = 0 ;

    private IStrategy strategy ;

    //    策略模式
    public int execute(int a , int b){
        return strategy.caculate(a,b);
    }

    public void reset(){
        this.now = 0 ;
    }

    //    簡單工廠模式
    public void setStrategy(DoType doType) {
        switch (doType){
            case ADD:
                this.strategy = new add();
                break;
            case MINUS:
               this.strategy = new minus();
                break;
            case DIVIDE:
                this.strategy = new divide();
                break;
            case MULTYPLY:
               this.strategy = new multyply();
                break;
        }
    }

    enum DoType{
        ADD , MINUS , DIVIDE , MULTYPLY
    }

}
```
## Example2
```
public interface IStrategy {
    public int calculate();
}
```
* Bus & MRT 的里程計價方式
```
public class BusStrategy implements IStrategy {
    @Override
    public int calculate(int km) {

//        一段票15元
//        十公里內一段票，超過十公里兩段票

        int count = 0 ;

        if( km <= 10 ){
            count = 1 ;
        }else if( km > 10){
            count = 2 ;
        }

        return count * 15 ;

    }
}

public class MRTStrategy implements IStrategy {
    @Override
    public int calculate(int km) {

//        小於十公里20元，超過每五公里多五元

        int result = 0 ;

        if(km <= 0) return  result ;

        if(km <= 10) {
            result = 20 ;
        }

        if(km > 10){
            int count = (int)Math.ceil((((double)km - 10) / 5));
            result = 20 + 5 * count ;
        }

        return result;

    }
}
```
* 依據里程數計價的計算機，只要選定你的移動方式（在這裡是 MRT or Bus)，就可以根據移動方式來計算出需要的費用。
```
public class PriceCalculator {
    IStrategy strategy;

    private PriceCalculator(){};

    // 這裡可以在建構子設定 strategy
    public PriceCalculator(IStrategy strategy){
        this.strategy = strategy;
    }
    // 也可以透過 setter 設定 strategy
    public void setStrategy(IStrategy strategy) {
        this.strategy = strategy;
    }

    public int calculate(int km){
        return this.calculate(km,strategy);
    }

    public int calculate(int km , IStrategy strategy){
        this.strategy = strategy;
        return strategy.calculate(km);
    }
}
```
## Example3
```
from abc import ABC, abstractmethod

# 付款策略介面
class PayStrategy(ABC):
    @abstractmethod
    def pay(self, amount):
        pass

# 信用卡付款
class CreditCardPay(PayStrategy):
    def pay(self, amount):
        print(f"用信用卡付款：{amount} 元")

# Line Pay 付款
class LinePay(PayStrategy):
    def pay(self, amount):
        print(f"用 Line Pay 付款：{amount} 元")

# 結帳上下文
class Checkout:
    def __init__(self, strategy: PayStrategy):
        self.strategy = strategy

    def set_strategy(self, strategy: PayStrategy):
        self.strategy = strategy

    def pay_bill(self, amount):
        self.strategy.pay(amount)

# 使用範例
checkout = Checkout(CreditCardPay())
checkout.pay_bill(500)  # 👉 用信用卡付款：500 元

checkout.set_strategy(LinePay())
checkout.pay_bill(300)  # 👉 用 Line Pay 付款：300 元
```
## Example4
```
from abc import ABC, abstractmethod

# 策略介面
class Strategy(ABC):
    @abstractmethod
    def execute(self, a, b):
        pass

# 策略 A：加法
class AddStrategy(Strategy):
    def execute(self, a, b):
        return a + b

# 策略 B：減法
class SubtractStrategy(Strategy):
    def execute(self, a, b):
        return a - b

# 上下文
class Calculator:
    def __init__(self, strategy: Strategy):
        self.strategy = strategy

    def set_strategy(self, strategy: Strategy):
        self.strategy = strategy

    def calculate(self, a, b):
        return self.strategy.execute(a, b)

# 用法
calc = Calculator(AddStrategy())
print(calc.calculate(5, 3))  # 輸出 8

calc.set_strategy(SubtractStrategy())
print(calc.calculate(5, 3))  # 輸出 2
```
## 心得
1. 將程式中容易變動的行為 (演算法)，獨立出來，不要和不需要變動的程式碼混在一起
2. 將這些演算法做分類，並為該類的演算法建立 interface
3. 繼承該 interface，並實作這些演算法
4. 使用者類別建立 interface 的 setter，供動態設定演算法 (這裡有用到多型)
