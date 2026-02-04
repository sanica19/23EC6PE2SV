// File        :vending_machine.sv
// Author      :Sanica M S /1BM23EC229
// Created     :04-02-2026
// Module      :vending
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :FSM tracks inserted coins and dispenses an item when total value reaches 15 cents.
module tb;

  logic clk = 0;
  logic rst;
  logic [4:0] coin;
  logic dispense;

  // Clock generation
  always #5 clk = ~clk;

  // DUT Instance
  vending dut (
    .clk(clk),
    .rst(rst),
    .coin(coin),
    .dispense(dispense)
  );

  // ---------------- WAVEFORM DUMP ----------------
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, tb);
  end

  // ---------------- COVERAGE ----------------
  covergroup cg_vend @(posedge clk);
    cp_state : coverpoint dut.state;
    cp_coin  : coverpoint coin;
    cp_disp  : coverpoint dispense;
  endgroup

  cg_vend cov = new();

  // ---------------- STIMULUS ----------------
  initial begin
    rst = 1;
    coin = 0;
    #12 rst = 0;

    repeat (20) begin
      case ($urandom_range(0,2))
        0: coin = 0;
        1: coin = 5;
        2: coin = 10;
      endcase
      @(posedge clk);
    end

    $display("Coverage = %0.2f %%", cov.get_coverage());
    $finish;
  end

endmodule
