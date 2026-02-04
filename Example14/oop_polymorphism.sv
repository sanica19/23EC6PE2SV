// File        :OOP_Polymerism.sv
// Author      :Sanica M S /1BM23EC229
// Created     :04-02-2026
// Module      :OOP
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :Demonstrates inheritance where a child class overrides the packet print behavior.
class Packet;
  rand bit [7:0] data;

  virtual function void print();
    $display("Normal: %h", data);
  endfunction
endclass

class BadPacket extends Packet;
  virtual function void print();
    $display("ERROR: %h", data);
  endfunction
endclass
