// File        :OOP_Polymerism_tb.sv
// Author      :Sanica M S /1BM23EC229
// Created     :04-02-2026
// Module      :OOP
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :Demonstrates inheritance where a child class overrides the packet print behavior.

module tb;

  Packet p;
  BadPacket bad = new();

  bit clk = 0;
  bit [7:0] data_sig;   // signal for waveform

  always #5 clk = ~clk;

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;

    p = bad;

    if (!p.randomize())
      $display("Randomization failed");

    data_sig = p.data;   // move class data to signal
    p.print();

    #20;
    $finish;
  end

endmodule
