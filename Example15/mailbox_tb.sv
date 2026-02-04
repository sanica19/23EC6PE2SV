// File        :mailbox_tb.sv
// Author      :Sanica M S/1BM23EC229
// Created     :04-02-2026
// Module      :mailbox_tb
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :Testbench demonstrates generator and driver communicating safely using a mailbox in parallel execution.
module tb;

  mailbox #(Packet) mbx = new();

  bit clk = 0;
  bit [7:0] data_sig;

  always #5 clk = ~clk;

  task generator();
    Packet p;
    repeat (5) begin
      p = new();
      p.randomize();
      mbx.put(p);
      @(posedge clk);
    end
  endtask

  task driver();
    Packet p;
    repeat (5) begin
      mbx.get(p);
      data_sig = p.val;
      @(posedge clk);
    end
  endtask

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;

    fork
      generator();
      driver();
    join

    #20 $finish;
  end

endmodule
