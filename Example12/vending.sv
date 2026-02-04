// File        :vending.sv
// Author      :Sanica M S /1BM23EC229
// Created     :04-02-2026
// Module      :vending
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :FSM tracks inserted coins and dispenses an item when total value reaches 15 cents.
module vending (
    input  logic       clk,
    input  logic       rst,
    input  logic [4:0] coin,
    output logic       dispense
);

  typedef enum logic [1:0] {IDLE, HAS5, HAS10} state_t;
  state_t state, next_state;

  // State register
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      state <= IDLE;
    else
      state <= next_state;
  end

  // Next-state and output logic
  always_comb begin
    next_state = state;
    dispense   = 0;

    case (state)

      IDLE: begin
        if (coin == 5)
          next_state = HAS5;
        else if (coin == 10)
          next_state = HAS10;
      end

      HAS5: begin
        if (coin == 5)
          next_state = HAS10;          // 5 + 5 = 10
        else if (coin == 10) begin
          next_state = IDLE;           // 5 + 10 = 15
          dispense   = 1;
        end
      end

      HAS10: begin
        if (coin == 5) begin
          next_state = IDLE;           // 10 + 5 = 15
          dispense   = 1;
        end
        else if (coin == 10) begin
          next_state = IDLE;           // 10 + 10 = 20
          dispense   = 1;
        end
      end

    endcase
  end

endmodule
