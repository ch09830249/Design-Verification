program card_game;

    typedef enum {SPADE, HEART, DIAMOND, CLUB} suit_t;
    typedef int unsigned rank_t; // 1 ~ 13

    // 一張牌
    class card;
        rand suit_t suit;
        rand rank_t rank;

        function string str();
            string s;
            case (suit)
                SPADE:   s = "♠";
                HEART:   s = "♥";
                DIAMOND: s = "♦";
                CLUB:    s = "♣";
            endcase
            return {s, $sformatf("%0d", rank)};
        endfunction
    endclass

    // 發牌器
    class dealer;
        card deck[52];         // 一副牌
        card hands[4][13];     // 每人 13 張

        function void build_deck();
            int idx = 0;
            foreach (deck[i]) begin
                for (int s = 0; s < 4; s++) begin
                    for (int r = 1; r <= 13; r++) begin
                        deck[idx] = new();
                        deck[idx].suit = suit_t'(s);
                        deck[idx].rank = r;
                        idx++;
                    end
                end
            end
        endfunction

        function void shuffle();
            // Fisher–Yates 洗牌演算法
            card temp;
            for (int i = 51; i > 0; i--) begin
                int j = $urandom_range(0, i);
                temp = deck[i];
                deck[i] = deck[j];
                deck[j] = temp;
            end
        endfunction

        function void deal();
            int d = 0;
            for (int p = 0; p < 4; p++) begin
                for (int c = 0; c < 13; c++) begin
                    hands[p][c] = deck[d++];
                end
            end
        endfunction

        function void print();
            for (int p = 0; p < 4; p++) begin
                $display("Player %0d:", p+1);
                foreach (hands[p][c])
                    $write("%s ", hands[p][c].str());
                $display("\n");
            end
        endfunction
    endclass

    // 主程式
    initial begin
        dealer d = new();

        d.build_deck();
        d.shuffle();
        d.deal();
        d.print();
    end

endprogram

/*
	Player 1:
	♣3 ♥8 ♦12 ♠5 ♦6 ♣10 ♥12 ♥1 ♥3 ♣4 ♦1 ♠9 ♣9

	Player 2:
	♠13 ♦4 ♥10 ♠11 ♠10 ♥2 ♦3 ♠1 ♠3 ♠6 ♦5 ♣11 ♠12

	Player 3:
	♣2 ♥7 ♣6 ♦7 ♦2 ♦11 ♣5 ♠7 ♦10 ♥4 ♠2 ♥13 ♥6

	Player 4:
	♣1 ♣7 ♦9 ♣13 ♠4 ♦13 ♣8 ♠8 ♣12 ♦8 ♥11 ♥9 ♥5
*/