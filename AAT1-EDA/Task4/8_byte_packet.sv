//------------------------------------------------------------------------------
//File       : 8_byte_packet.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 04-02-2026
//Module     : Ethpacket
//Project    : SystemVerilog and Verification (23EC6PE2SV)
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: A placeholder dummy DUT for the class-based Packet verification lab.
//------------------------------------------------------------------------------
`timescale 1ns/1ps

class EthPacket;

  rand int unsigned len;
  rand byte payload[];

  // Length between 4 and 8 bytes
  constraint len_c {
    len inside {[4:8]};
  }

  // Payload size must match length
  constraint payload_c {
    payload.size() == len;
  }

  function void display();
    $display("len=%0d payload_size=%0d payload=%p",
              len, payload.size(), payload);
  endfunction

endclass
