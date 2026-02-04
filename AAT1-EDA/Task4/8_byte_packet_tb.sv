//------------------------------------------------------------------------------
//File       : 8_byte_packet_tb.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 04-02-2026
//Module     : eth_packet_tb
//Project    : SystemVerilog and Verification (23EC6PE2SV)
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: A placeholder dummy DUT for the class-based Packet verification lab.
//------------------------------------------------------------------------------
`timescale 1ns/1ps

module eth_packet_tb;

  EthPacket pkt;

  // Visible TB signals
  int len_mon;
  int payload_size_mon;
  logic clk;

  // Clock for clean waveform
  always #5 clk = ~clk;

  // Coverage
  covergroup pkt_cg @(posedge clk);
    coverpoint len_mon {
      bins b4 = {4};
      bins b5 = {5};
      bins b6 = {6};
      bins b7 = {7};
      bins b8 = {8};
    }
  endgroup

  pkt_cg cg;

  initial begin
    clk = 0;
    pkt = new();
    cg  = new();

    // Dump ONLY required signals
    $dumpfile("eth_packet.vcd");
    $dumpvars(0, clk, len_mon, payload_size_mon);

    $display("---- Ethernet Packet Randomization ----");

    repeat (25) begin
      assert(pkt.randomize())
        else $fatal("Randomization failed");

      // Copy class values into TB signals
      len_mon          = pkt.len;
      payload_size_mon = pkt.payload.size();

      pkt.display();
      cg.sample();

      @(posedge clk);
    end

    $display("Coverage = %0.2f%%", cg.get_coverage());
    $finish;
  end

endmodule
