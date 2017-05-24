mod opcodes;

use std::fmt;
use self::opcodes::{Mode, Name, Opcode};

const NMI_VECTOR: u16 = 0xFFFA;
const RESET_VECTOR: u16 = 0xFFFC;
const IRQ_VECTOR: u16 = 0xFFFE;
const MEMORY_SIZE: usize = 65_536;

#[derive(Debug, Copy, Clone, PartialEq)]
enum Operand {
    Accumulator,
    Value(u8),
    Address(u16),
}

enum Status {
    C = 1,
    Z = 1 << 1,
    I = 1 << 2,
    D = 1 << 3,
    B = 1 << 4,
    V = 1 << 6,
    S = 1 << 7,
}

struct CPU {
    acc: u8,
    x: u8,
    y: u8,
    status: u8,
    sp: u8,
    pc: u16,
    mem: Vec<u8>,
    break_at: u16,
    debug: bool,
}

impl fmt::Display for CPU {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,
               "CPU(acc: {}, x: {}, y: {}, status: 0b{:08b}, sp: {:#02X}, pc: {:#04X})",
               self.acc,
               self.x,
               self.y,
               self.status,
               self.sp,
               self.pc)
    }
}

impl CPU {
    pub fn new() -> Self {
        Self {
            acc: 0,
            x: 0,
            y: 0,
            status: 0x20,
            sp: 0xFF,
            pc: 0,
            mem: vec![0; MEMORY_SIZE],
            break_at: 0xFFFF,
            debug: false,
        }
    }

    pub fn reset(&mut self) {
        self.acc = 0;
        self.x = 0;
        self.y = 0;
        self.pc = self.read_two(RESET_VECTOR);
        self.status = 0x20;
    }

    pub fn irq(&mut self) {
        if !self.get_status(Status::I) {
            let pc = self.pc;

            self.set_status(Status::B, false);
            let status = self.status;

            self.push_two(pc);
            self.push_one(status);
            self.sei();
            self.pc = self.read_two(IRQ_VECTOR);
        }
    }

    pub fn nmi(&mut self) {
        let pc = self.pc;

        self.set_status(Status::B, false);
        let status = self.status;

        self.push_two(pc);
        self.push_one(status);
        self.sei();
        self.pc = self.read_two(NMI_VECTOR);
    }

    pub fn load_ram(&mut self, mem: Vec<u8>, offset: u16) {
        self.pc = offset;

        for (i, byte) in mem.into_iter().enumerate() {
            self.mem[offset as usize + i] = byte;
        }
    }

    pub fn execute(&mut self) {
        while self.pc != self.break_at {
            let opcode = self.read_one(self.pc);

            match Opcode::get_by_code(opcode) {
                Some(op) => self.tick(op),
                None => panic!("invalid opcode {:#02X}", opcode),
            }
        }
    }

    pub fn tick(&mut self, opcode: &Opcode) {
        let operand = self.operand_for_mode(opcode.mode);
        let val = self.value_for_operand(&operand);
        let addr = self.addr_for_operand(&operand);
        if self.debug {
            self.debug(opcode, operand, val, addr);
        }
        self.pc += opcode.bytes as u16;

        match opcode.name {
            Name::ADC => self.adc(val),
            Name::AND => self.and(val),
            Name::ASL => self.asl(&operand),
            Name::BCC => self.bcc(val),
            Name::BCS => self.bcs(val),
            Name::BEQ => self.beq(val),
            Name::BIT => self.bit(val),
            Name::BMI => self.bmi(val),
            Name::BNE => self.bne(val),
            Name::BPL => self.bpl(val),
            Name::BRK => self.brk(),
            Name::BVC => self.bvc(val),
            Name::BVS => self.bvs(val),
            Name::CLC => self.clc(),
            Name::CLD => self.cld(),
            Name::CLI => self.cli(),
            Name::CLV => self.clv(),
            Name::CMP => self.cmp(val),
            Name::CPX => self.cpx(val),
            Name::CPY => self.cpy(val),
            Name::DEC => self.dec(addr),
            Name::DEX => self.dex(),
            Name::DEY => self.dey(),
            Name::EOR => self.eor(val),
            Name::INC => self.inc(addr),
            Name::INX => self.inx(),
            Name::INY => self.iny(),
            Name::JMP => self.jmp(addr),
            Name::JSR => self.jsr(addr),
            Name::LDA => self.lda(val),
            Name::LDX => self.ldx(val),
            Name::LDY => self.ldy(val),
            Name::LSR => self.lsr(&operand),
            Name::NOP => {}
            Name::ORA => self.ora(val),
            Name::PHA => self.pha(),
            Name::PHP => self.php(),
            Name::PLA => self.pla(),
            Name::PLP => self.plp(),
            Name::ROL => self.rol(&operand),
            Name::ROR => self.ror(&operand),
            Name::RTI => self.rti(),
            Name::RTS => self.rts(),
            Name::SBC => self.sbc(val),
            Name::SEC => self.sec(),
            Name::SED => self.sed(),
            Name::SEI => self.sei(),
            Name::STA => self.sta(addr),
            Name::STX => self.stx(addr),
            Name::STY => self.sty(addr),
            Name::TAX => self.tax(),
            Name::TAY => self.tay(),
            Name::TSX => self.tsx(),
            Name::TXA => self.txa(),
            Name::TXS => self.txs(),
            Name::TYA => self.tya(),
        };
    }

    fn adc(&mut self, val: u8) {
        let carry = self.get_status(Status::C) as u8;
        let a = self.acc;
        let mut result = a as u16 + val as u16 + carry as u16;

        if self.get_status(Status::D) {
            self.set_status(Status::Z, result as u8 == 0);

            if (a & 0xF) + (val & 0xF) + carry > 9 {
                result += 6;
            }

            let v = (a ^ result as u8) & (val ^ result as u8) & 0x80 != 0;
            self.set_status(Status::S, result & 0x80 > 0);
            self.set_status(Status::V, v);

            if result > 0x99 {
                result += 96;
            }
        } else {
            let v = (a ^ result as u8) & (val ^ result as u8) & 0x80 != 0;

            self.set_status(Status::V, v);
            self.set_s_and_z(result as u8);
        }

        self.set_status(Status::C, result > 0xFF);
        self.acc = result as u8;
    }

    fn and(&mut self, val: u8) {
        let result = self.acc & val;
        self.acc = result;
        self.set_s_and_z(result);
    }

    fn asl(&mut self, operand: &Operand) {
        let old_val = self.value_for_operand(operand);
        let new_val = old_val << 1;
        self.set_operand(operand, new_val);
        self.set_status(Status::C, old_val & 0x80 > 0);
        self.set_s_and_z(new_val);
    }

    fn bcc(&mut self, offset: u8) {
        if !self.get_status(Status::C) {
            self.jump(offset);
        }
    }

    fn bcs(&mut self, offset: u8) {
        if self.get_status(Status::C) {
            self.jump(offset);
        }
    }

    fn beq(&mut self, offset: u8) {
        if self.get_status(Status::Z) {
            self.jump(offset);
        }
    }

    fn bit(&mut self, val: u8) {
        let result = self.acc & val;
        self.set_status(Status::Z, result == 0);
        self.set_status(Status::V, val & 0x40 > 0);
        self.set_status(Status::S, val & 0x80 > 0);
    }

    fn bmi(&mut self, offset: u8) {
        if self.get_status(Status::S) {
            self.jump(offset);
        }
    }

    fn bne(&mut self, offset: u8) {
        if !self.get_status(Status::Z) {
            self.jump(offset);
        }
    }

    fn bpl(&mut self, offset: u8) {
        if !self.get_status(Status::S) {
            self.jump(offset);
        }
    }

    fn brk(&mut self) {
        self.pc += 1;
        let pc = self.pc;

        self.set_status(Status::B, true);
        let status = self.status;

        self.push_two(pc);
        self.push_one(status);
        self.sei();
        self.pc = self.read_two(IRQ_VECTOR);
    }

    fn bvc(&mut self, offset: u8) {
        if !self.get_status(Status::V) {
            self.jump(offset);
        }
    }

    fn bvs(&mut self, offset: u8) {
        if self.get_status(Status::V) {
            self.jump(offset);
        }
    }

    fn clc(&mut self) {
        self.set_status(Status::C, false);
    }

    fn cld(&mut self) {
        self.set_status(Status::D, false);
    }

    fn cli(&mut self) {
        self.set_status(Status::I, false);
    }

    fn clv(&mut self) {
        self.set_status(Status::V, false);
    }

    fn cmp(&mut self, val: u8) {
        let result = self.acc as i16 - val as i16;
        self.set_status(Status::C, (result as u16) <= 0xFF);
        self.set_s_and_z(result as u8);
    }

    fn cpx(&mut self, val: u8) {
        let result = self.x as i16 - val as i16;
        self.set_status(Status::C, (result as u16) <= 0xFF);
        self.set_s_and_z(result as u8);
    }

    fn cpy(&mut self, val: u8) {
        let result = self.y as i16 - val as i16;
        self.set_status(Status::C, (result as u16) <= 0xFF);
        self.set_s_and_z(result as u8);
    }

    fn dec(&mut self, addr: u16) {
        let result = self.read_one(addr) as i16 - 1;
        self.write_one(addr, result as u8);
        self.set_s_and_z(result as u8);
    }

    fn dex(&mut self) {
        let result = self.x as i16 - 1;
        self.x = result as u8;
        self.set_s_and_z(result as u8);
    }

    fn dey(&mut self) {
        let result = self.y as i16 - 1;
        self.y = result as u8;
        self.set_s_and_z(result as u8);
    }

    fn eor(&mut self, val: u8) {
        let result = self.acc ^ val;
        self.acc = result;
        self.set_s_and_z(result);
    }

    fn inc(&mut self, addr: u16) {
        let result = (self.read_one(addr) as u16 + 1) as u8;
        self.write_one(addr, result);
        self.set_s_and_z(result);
    }

    fn inx(&mut self) {
        let x = (self.x as u16 + 1) as u8;
        self.x = x;
        self.set_s_and_z(x);
    }

    fn iny(&mut self) {
        let y = (self.y as u16 + 1) as u8;
        self.y = y;
        self.set_s_and_z(y);
    }

    fn jmp(&mut self, addr: u16) {
        self.pc = addr;
    }

    fn jsr(&mut self, addr: u16) {
        let pc = self.pc - 1;
        self.push_two(pc);
        self.pc = addr;
    }

    fn lda(&mut self, val: u8) {
        self.acc = val;
        self.set_s_and_z(val);
    }

    fn ldx(&mut self, val: u8) {
        self.x = val;
        self.set_s_and_z(val);
    }

    fn ldy(&mut self, val: u8) {
        self.y = val;
        self.set_s_and_z(val);
    }

    fn lsr(&mut self, operand: &Operand) {
        let old_val = self.value_for_operand(operand);
        let new_val = old_val >> 1;
        self.set_status(Status::C, old_val & 1 > 0);
        self.set_operand(operand, new_val);
        self.set_s_and_z(new_val);
    }

    fn ora(&mut self, val: u8) {
        let result = self.acc | val;
        self.acc = result;
        self.set_s_and_z(result);
    }

    fn pha(&mut self) {
        let a = self.acc;
        self.push_one(a);
    }

    fn php(&mut self) {
        let st = self.status | 0x30;
        self.push_one(st);
    }

    fn pla(&mut self) {
        let val = self.pop_one();

        self.acc = val;
        self.set_s_and_z(val);
    }

    fn plp(&mut self) {
        self.status = self.pop_one() | 0x20;
    }

    fn rol(&mut self, operand: &Operand) {
        let old_val = self.value_for_operand(operand) as u16;
        let mut new_val = old_val << 1;
        if self.get_status(Status::C) {
            new_val |= 1;
        }
        self.set_operand(operand, new_val as u8);
        self.set_status(Status::C, new_val > 0xFF);
        self.set_s_and_z(new_val as u8);
    }

    fn ror(&mut self, operand: &Operand) {
        let mut old_val = self.value_for_operand(operand) as u16;
        if self.get_status(Status::C) {
            old_val |= 0x100;
        }
        self.set_status(Status::C, old_val & 1 > 0);
        let new_val = old_val >> 1;
        self.set_operand(operand, new_val as u8);
        self.set_s_and_z(new_val as u8);
    }

    fn rti(&mut self) {
        self.status = self.pop_one() | 0x20;
        self.pc = self.pop_two();
    }

    fn rts(&mut self) {
        self.pc = self.pop_two() + 1;
    }

    fn sbc(&mut self, val: u8) {
        if self.get_status(Status::D) {
            self.adc(0x99 - val);
        } else {
            self.adc(0xFF - val);
        }
    }

    fn sec(&mut self) {
        self.set_status(Status::C, true);
    }

    fn sed(&mut self) {
        self.set_status(Status::D, true);
    }

    fn sei(&mut self) {
        self.set_status(Status::I, true);
    }

    fn sta(&mut self, addr: u16) {
        let a = self.acc;
        self.write_one(addr, a);
    }

    fn stx(&mut self, addr: u16) {
        let x = self.x;
        self.write_one(addr, x);
    }

    fn sty(&mut self, addr: u16) {
        let y = self.y;
        self.write_one(addr, y);
    }

    fn tax(&mut self) {
        let a = self.acc;
        self.x = a;
        self.set_s_and_z(a);
    }

    fn tay(&mut self) {
        let a = self.acc;
        self.y = a;
        self.set_s_and_z(a);
    }

    fn tsx(&mut self) {
        let sp = self.sp;
        self.x = sp;
        self.set_s_and_z(sp);
    }

    fn txa(&mut self) {
        let x = self.x;
        self.acc = x;
        self.set_s_and_z(x);
    }

    fn txs(&mut self) {
        self.sp = self.x;
    }

    fn tya(&mut self) {
        let y = self.y;
        self.acc = y;
        self.set_s_and_z(y);
    }

    fn set_operand(&mut self, operand: &Operand, val: u8) {
        match *operand {
            Operand::Accumulator => self.acc = val,
            _ => {
                let addr = self.addr_for_operand(operand);
                self.write_one(addr, val);
            }
        }
    }

    fn operand_for_mode(&self, mode: Mode) -> Operand {
        let pc = self.pc + 1;
        match mode {
            Mode::Absolute => Operand::Address(self.read_two(pc)),
            Mode::AbsoluteX => Operand::Address(self.x as u16 + self.read_two(pc)),
            Mode::AbsoluteY => Operand::Address(self.y as u16 + self.read_two(pc)),
            Mode::ZeroPage => Operand::Address((self.read_one(pc) as u16) & 0xFF),
            Mode::ZeroPageX => Operand::Address((self.x as u16 + self.read_one(pc) as u16) & 0xFF),
            Mode::ZeroPageY => Operand::Address((self.y as u16 + self.read_one(pc) as u16) & 0xFF),
            Mode::Indirect => Operand::Address(self.read_two(self.read_two(pc))),
            Mode::IndirectX => {
                let addr = (self.x as u16 + self.read_one(pc) as u16) & 0xFF;
                Operand::Address(self.read_two(addr))
            }
            Mode::IndirectY => {
                Operand::Address(self.y as u16 + self.read_two(self.read_one(pc) as u16))
            }
            Mode::Immediate | Mode::Relative => Operand::Value(self.read_one(pc)),
            Mode::Accumulator => Operand::Accumulator,
            Mode::Implied => Operand::Value(0),
        }
    }

    fn value_for_operand(&self, operand: &Operand) -> u8 {
        match *operand {
            Operand::Accumulator => self.acc,
            Operand::Value(val) => val,
            Operand::Address(addr) => self.read_one(addr),
        }
    }

    fn addr_for_operand(&self, operand: &Operand) -> u16 {
        match *operand {
            Operand::Accumulator => self.acc as u16,
            Operand::Value(val) => val as u16,
            Operand::Address(addr) => addr,
        }
    }

    fn read_one(&self, addr: u16) -> u8 {
        self.mem[addr as usize]
    }

    fn read_two(&self, addr: u16) -> u16 {
        let low = self.read_one(addr) as u16;
        let high = self.read_one(addr + 1) as u16;
        (high << 8) | low
    }

    fn write_one(&mut self, addr: u16, val: u8) {
        self.mem[addr as usize] = val;
    }

    fn get_status(&self, s: Status) -> bool {
        self.status & (s as u8) > 0
    }

    fn set_status(&mut self, s: Status, val: bool) {
        match val {
            true => self.status |= s as u8,
            false => self.status &= !(s as u8),
        }
    }

    fn set_s_and_z(&mut self, val: u8) {
        self.set_status(Status::S, val >= 0x80);
        self.set_status(Status::Z, val == 0);
    }

    fn jump(&mut self, offset: u8) {
        if offset >= 0x80 {
            self.pc -= 256 - offset as u16
        } else {
            self.pc += offset as u16
        }
    }

    fn push_two(&mut self, val: u16) {
        self.push_one((val >> 8) as u8);
        self.push_one((val & 0xFF) as u8);
    }

    fn push_one(&mut self, val: u8) {
        let addr = self.sp as u16 + 0x100;
        self.write_one(addr, val);
        self.sp = ((self.sp as i16 - 1) & 0xFF) as u8;
    }

    fn pop_two(&mut self) -> u16 {
        let low = self.pop_one() as u16;
        let high = self.pop_one() as u16;
        (high << 8) | low
    }

    fn pop_one(&mut self) -> u8 {
        self.sp = ((self.sp as u16 + 1) & 0xFF) as u8;
        let addr = self.sp as u16 + 0x100;
        self.read_one(addr)
    }

    fn debug(&self, opcode: &Opcode, operand: Operand, val: u8, addr: u16) {
        println!("Performing {:?}. {}", opcode.name, self);
        println!("&Opcode ({:#02X}): {:?}", opcode.code, opcode);
        println!("Operand: {:?}, Value: {}, Address: {:#02X}\n",
                 operand,
                 val,
                 addr);
    }
}

#[cfg(test)]
mod test {
    use std::fs::File;
    use std::io::Read;
    use std::path::Path;

    use super::*;

    #[test]
    #[should_panic]
    fn test_invalid_opcode() {
        let mut cpu = CPU::new();
        cpu.load_ram(vec![0xff], 0);
        cpu.execute();
    }

    #[test]
    fn test_set_s_and_z() {
        let mut cpu = CPU::new();

        cpu.set_s_and_z(0b10000000);
        assert!(cpu.get_status(Status::S));
        assert!(!cpu.get_status(Status::Z));

        cpu.set_s_and_z(0);
        assert!(!cpu.get_status(Status::S));
        assert!(cpu.get_status(Status::Z));
    }

    #[test]
    fn test_operand_for_opcode() {
        let mut cpu = CPU::new();
        cpu.load_ram(vec![0, 0, 1, 2, 3], 0);
        // for indirect addressing
        cpu.write_one(0x0101, 0);
        cpu.write_one(0x0102, 0);
        cpu.write_one(0x0202, 1);
        cpu.write_one(0x0203, 1);
        cpu.write_one(0x0303, 2);
        cpu.write_one(0x0304, 2);
        cpu.pc = 0; // read_one => 0, read_two => 0x0100
        cpu.x = 1; // read_one => 1, read_two => 0x0201
        cpu.y = 2; // read_one => 2, read_two => 0x0302
        let expecteds = vec![(Mode::Absolute, Operand::Address(0x0100)),
                             (Mode::AbsoluteX, Operand::Address(1 + 0x0100)),
                             (Mode::AbsoluteY, Operand::Address(2 + 0x0100)),
                             (Mode::ZeroPage, Operand::Address(0)),
                             (Mode::ZeroPageX, Operand::Address(1)),
                             (Mode::ZeroPageY, Operand::Address(2)),
                             (Mode::Indirect, Operand::Address(0)),
                             (Mode::IndirectX, Operand::Address(256)),
                             (Mode::IndirectY, Operand::Address(2)),
                             (Mode::Immediate, Operand::Value(0)),
                             (Mode::Relative, Operand::Value(0)),
                             (Mode::Accumulator, Operand::Accumulator),
                             (Mode::Implied, Operand::Value(0))];

        for (input, output) in expecteds {
            println!("testing {} {:?}", input, output);
            assert_eq!(cpu.operand_for_mode(input), output)
        }
    }

    #[test]
    fn test_value_for_operand() {
        let mut cpu = CPU::new();
        cpu.acc = 2;
        cpu.load_ram(vec![1, 2, 3], 0);

        let expecteds =
            vec![(Operand::Accumulator, 2), (Operand::Value(1), 1), (Operand::Address(2), 3)];

        for (input, output) in expecteds {
            assert_eq!(cpu.value_for_operand(&input), output);
        }
    }

    #[test]
    fn test_addr_for_operand() {
        let mut cpu = CPU::new();
        cpu.acc = 2;

        let expecteds =
            vec![(Operand::Accumulator, 2), (Operand::Value(1), 1), (Operand::Address(2), 2)];

        for (input, output) in expecteds {
            assert_eq!(cpu.addr_for_operand(&input), output);
        }
    }

    #[test]
    fn test_read_one() {
        let mut cpu = CPU::new();
        cpu.load_ram(vec![22, 23, 24], 0);

        assert_eq!(cpu.read_one(1), 23);
    }

    #[test]
    fn test_read_two() {
        let mut cpu = CPU::new();
        cpu.load_ram(vec![0xC7, 0xD7, 0xE7], 0);

        assert_eq!(cpu.read_two(1), 0xE7D7);
    }

    #[test]
    fn test_write_one() {
        let mut cpu = CPU::new();
        cpu.write_one(1, 55);
        assert_eq!(cpu.mem[1], 55);
    }

    #[test]
    fn test_push_one_pop_one() {
        let mut cpu = CPU::new();
        cpu.push_one(3);
        assert_eq!(cpu.sp, 0xFE);
        assert_eq!(cpu.pop_one(), 3);
        assert_eq!(cpu.sp, 0xFF);
    }

    #[test]
    fn test_push_two_pop_two() {
        let mut cpu = CPU::new();
        cpu.push_two(0xCCDD);
        assert_eq!(cpu.sp, 0xFD);
        assert_eq!(cpu.pop_two(), 0xCCDD);
        assert_eq!(cpu.sp, 0xFF);
    }

    #[test]
    fn test_reset() {
        let mut cpu = CPU::new();
        cpu.write_one(RESET_VECTOR, 0x40);
        cpu.write_one(RESET_VECTOR + 1, 0x20);
        cpu.acc = 20;
        cpu.x = 21;
        cpu.y = 22;
        cpu.pc = 300;
        cpu.reset();
        assert_eq!(cpu.acc, 0);
        assert_eq!(cpu.x, 0);
        assert_eq!(cpu.y, 0);
        assert_eq!(cpu.status, 0x20);
        assert_eq!(cpu.pc, 0x2040);
    }

    #[test]
    fn test_nmi() {
        let mut cpu = CPU::new();
        cpu.pc = 10;
        cpu.status = 0b11100011;
        cpu.nmi();

        assert!(!cpu.get_status(Status::B), "break");
        assert_eq!(cpu.pop_one(), 0b11100011, "saved status");
        assert_eq!(cpu.pop_two(), 10, "saved pc");
        assert_eq!(cpu.pc, 0, "pc");
    }

    #[test]
    fn test_irq_when_not_interrupt() {
        let mut cpu = CPU::new();
        cpu.pc = 10;
        cpu.status = 0b11110011;
        cpu.irq();

        assert!(!cpu.get_status(Status::B), "break");
        assert_eq!(cpu.pop_one(), 0b11100011, "saved status");
        assert_eq!(cpu.pop_two(), 10, "saved pc");
        assert_eq!(cpu.pc, 0, "pc");
    }

    #[test]
    // should not execute
    fn test_irq_when_interrupt() {
        let mut cpu = CPU::new();
        cpu.pc = 10;
        cpu.status = 0b00110100;
        cpu.irq();

        assert_eq!(cpu.pc, 10);
        assert_eq!(cpu.status, 0b00110100);
    }

    // opcode execution tests
    #[test]
    fn test_adc() {
        let mut cpu = CPU::new();
        let expecteds = vec![((80, 16, false), (96, false, false)),
                             ((80, 80, false), (160, false, true)),
                             ((80, 144, false), (224, false, false)),
                             ((80, 208, false), (32, true, false)),
                             ((208, 16, false), (224, false, false)),
                             ((208, 80, true), (33, true, false)),
                             ((208, 144, true), (97, true, true)),
                             ((208, 208, true), (161, true, false))];

        for expected in expecteds {
            let input = expected.0;
            let output = expected.1;
            cpu.acc = input.0;
            cpu.set_status(Status::C, input.2);
            cpu.set_status(Status::V, false);
            cpu.adc(input.1);
            assert_eq!(cpu.acc, output.0, "computation");
            assert_eq!(cpu.get_status(Status::C), output.1, "carry");
            assert_eq!(cpu.get_status(Status::V), output.2, "overflow");
        }
    }

    #[test]
    fn test_adc_decimal_mode() {
        let mut cpu = CPU::new();
        cpu.set_status(Status::D, true);

        let expecteds = vec![((0x58, 0x46, true), (0x05, true, true)),
                             ((0x12, 0x34, false), (0x46, false, false)),
                             ((0x15, 0x26, false), (0x41, false, false)),
                             ((0x81, 0x92, false), (0x73, true, true))];

        for expected in expecteds {
            let input = expected.0;
            let output = expected.1;
            cpu.acc = input.0;
            cpu.set_status(Status::C, input.2);
            cpu.set_status(Status::V, false);
            cpu.adc(input.1);
            println!("testing {:#02X}", output.0);
            assert_eq!(cpu.acc, output.0, "computation");
            assert_eq!(cpu.get_status(Status::C), output.1, "carry");
            assert_eq!(cpu.get_status(Status::V), output.2, "overflow");
        }
    }

    #[test]
    fn test_and() {
        let mut cpu = CPU::new();
        let expecteds = vec![((0b11001100, 0b00110011), (0, false, true)),
                             ((0b11001100, 0b10110011), (128, true, false))];

        for (input, output) in expecteds {
            cpu.acc = input.0;
            cpu.and(input.1);
            assert_eq!(cpu.acc, output.0, "result");
            assert_eq!(cpu.get_status(Status::S), output.1, "negative");
            assert_eq!(cpu.get_status(Status::Z), output.2, "zero");
        }
    }

    #[test]
    fn test_asl_acc() {
        let mut cpu = CPU::new();
        cpu.acc = 2;
        cpu.asl(&Operand::Accumulator);
        assert_eq!(cpu.acc, 4);
        assert!(!cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_asl_mem() {
        let mut cpu = CPU::new();
        cpu.acc = 0;
        cpu.load_ram(vec![0, 0xFF], 0);
        cpu.asl(&Operand::Address(1));
        assert_eq!(cpu.read_one(1), 0xFE);
        assert!(cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(cpu.get_status(Status::S));
    }

    #[test]
    fn test_jump() {
        let mut cpu = CPU::new();
        cpu.jump(100);
        assert_eq!(cpu.pc, 100);

        cpu.jump(200);
        assert_eq!(cpu.pc, 44);
    }

    #[test]
    fn test_branching_when_clear() {
        let mut cpu = CPU::new();
        cpu.status = 0;

        cpu.bcs(10);
        assert_eq!(cpu.pc, 0);
        cpu.beq(10);
        assert_eq!(cpu.pc, 0);
        cpu.bmi(10);
        assert_eq!(cpu.pc, 0);
        cpu.bvs(10);
        assert_eq!(cpu.pc, 0);

        cpu.bcc(10);
        assert_eq!(cpu.pc, 10);
        cpu.bne(10);
        assert_eq!(cpu.pc, 20);
        cpu.bpl(10);
        assert_eq!(cpu.pc, 30);
        cpu.bvc(10);
        assert_eq!(cpu.pc, 40);
    }

    #[test]
    fn test_branching_when_set() {
        let mut cpu = CPU::new();
        cpu.status = 0xFF;

        cpu.bcs(10);
        assert_eq!(cpu.pc, 10);
        cpu.beq(10);
        assert_eq!(cpu.pc, 20);
        cpu.bmi(10);
        assert_eq!(cpu.pc, 30);
        cpu.bvs(10);
        assert_eq!(cpu.pc, 40);

        cpu.bcc(10);
        assert_eq!(cpu.pc, 40);
        cpu.bne(10);
        assert_eq!(cpu.pc, 40);
        cpu.bpl(10);
        assert_eq!(cpu.pc, 40);
        cpu.bvc(10);
        assert_eq!(cpu.pc, 40);
    }

    #[test]
    fn test_bit() {
        let mut cpu = CPU::new();
        cpu.acc = 0xFF;

        cpu.bit(0);
        assert!(cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::V));
        assert!(!cpu.get_status(Status::S));

        cpu.bit(0xFF);
        assert!(!cpu.get_status(Status::Z));
        assert!(cpu.get_status(Status::V));
        assert!(cpu.get_status(Status::S));
    }

    #[test]
    fn test_brk() {
        let mut cpu = CPU::new();
        cpu.pc = 10;
        cpu.status = 0b11000011;
        cpu.brk();

        assert!(cpu.get_status(Status::B), "break");
        assert_eq!(cpu.pop_one(), 0b11010011, "saved status");
        assert_eq!(cpu.pop_two(), 11, "saved pc");
        assert_eq!(cpu.pc, 0, "pc");
    }

    #[test]
    fn test_clearing() {
        let mut cpu = CPU::new();
        cpu.status = 0xFF;
        cpu.clc();
        assert!(!cpu.get_status(Status::C));
        cpu.cld();
        assert!(!cpu.get_status(Status::D));
        cpu.cli();
        assert!(!cpu.get_status(Status::I));
        cpu.clv();
        assert!(!cpu.get_status(Status::V));
    }

    #[test]
    fn test_cmp() {
        let mut cpu = CPU::new();
        cpu.acc = 100;
        cpu.cmp(20);
        assert!(cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));

        cpu.acc = 100;
        cpu.cmp(120);
        assert!(!cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(cpu.get_status(Status::S));
    }

    #[test]
    fn test_cpx() {
        let mut cpu = CPU::new();
        cpu.x = 100;
        cpu.cpx(20);
        assert!(cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));

        cpu.x = 100;
        cpu.cpx(120);
        assert!(!cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(cpu.get_status(Status::S));
    }

    #[test]
    fn test_cpy() {
        let mut cpu = CPU::new();
        cpu.y = 100;
        cpu.cpy(20);
        assert!(cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));

        cpu.y = 100;
        cpu.cpy(120);
        assert!(!cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(cpu.get_status(Status::S));
    }

    #[test]
    fn test_dec() {
        let mut cpu = CPU::new();
        cpu.load_ram(vec![3, 4, 5], 0);
        cpu.dec(1);
        assert_eq!(cpu.mem[1], 3);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_dex() {
        let mut cpu = CPU::new();
        cpu.x = 3;
        cpu.dex();
        assert_eq!(cpu.x, 2);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_dey() {
        let mut cpu = CPU::new();
        cpu.y = 3;
        cpu.dey();
        assert_eq!(cpu.y, 2);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_eor() {
        let mut cpu = CPU::new();
        cpu.acc = 0b11001100;
        cpu.eor(0b11000000);
        assert_eq!(cpu.acc, 0b00001100);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_inc() {
        let mut cpu = CPU::new();
        cpu.load_ram(vec![3, 4, 5], 0);
        cpu.inc(1);
        assert_eq!(cpu.mem[1], 5);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_inx() {
        let mut cpu = CPU::new();
        cpu.x = 3;
        cpu.inx();
        assert_eq!(cpu.x, 4);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_iny() {
        let mut cpu = CPU::new();
        cpu.y = 3;
        cpu.iny();
        assert_eq!(cpu.y, 4);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_jmp() {
        let mut cpu = CPU::new();
        cpu.jmp(24);
        assert_eq!(cpu.pc, 24);
    }

    #[test]
    fn test_jsr() {
        let mut cpu = CPU::new();
        cpu.pc = 10;
        cpu.jsr(24);
        assert_eq!(cpu.pc, 24);
        assert_eq!(cpu.pop_two(), 9);
    }

    #[test]
    fn test_lda() {
        let mut cpu = CPU::new();
        cpu.lda(128);
        assert_eq!(cpu.acc, 128);
        assert!(!cpu.get_status(Status::Z));
        assert!(cpu.get_status(Status::S));
    }

    #[test]
    fn test_ldx() {
        let mut cpu = CPU::new();
        cpu.x = 7;
        cpu.ldx(0);
        assert_eq!(cpu.x, 0);
        assert!(cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_ldy() {
        let mut cpu = CPU::new();
        cpu.ldy(10);
        assert_eq!(cpu.y, 10);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_lsr_acc() {
        let mut cpu = CPU::new();
        cpu.acc = 0b100;
        cpu.lsr(&Operand::Accumulator);
        assert_eq!(cpu.acc, 0b10);
        assert!(!cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_lsr_mem() {
        let mut cpu = CPU::new();
        cpu.load_ram(vec![0b10000001], 0);
        cpu.lsr(&Operand::Address(0));
        assert_eq!(cpu.read_one(0), 0b01000000);
        assert!(cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_ora() {
        let mut cpu = CPU::new();
        cpu.acc = 0b01000000;
        cpu.ora(0b10000000);
        assert_eq!(cpu.acc, 0b11000000);
        assert!(cpu.get_status(Status::S));
        assert!(!cpu.get_status(Status::Z));
    }

    #[test]
    fn test_pha() {
        let mut cpu = CPU::new();
        cpu.acc = 10;
        cpu.pha();
        assert_eq!(cpu.sp, 0xFE);
        assert_eq!(cpu.mem[0x1FF], 10);
    }

    #[test]
    fn test_php() {
        let mut cpu = CPU::new();
        cpu.status = 0b00100011;
        cpu.php();
        assert_eq!(cpu.sp, 0xFE);
        assert_eq!(cpu.mem[0x1FF], 0b00110011);
    }

    #[test]
    fn test_pla() {
        let mut cpu = CPU::new();
        cpu.sp = 0xFE;
        cpu.mem[0x1FF] = 0b10000000;
        cpu.pla();
        assert_eq!(cpu.sp, 0xFF);
        assert_eq!(cpu.acc, 0b10000000);
        assert!(cpu.get_status(Status::S));
        assert!(!cpu.get_status(Status::Z));
    }

    #[test]
    fn test_plp() {
        let mut cpu = CPU::new();
        cpu.sp = 0xFE;
        cpu.mem[0x1FF] = 50;
        cpu.plp();
        assert_eq!(cpu.sp, 0xFF);
        assert_eq!(cpu.status, 50);
    }

    #[test]
    fn test_rol_acc() {
        let mut cpu = CPU::new();
        cpu.acc = 0b100;
        cpu.set_status(Status::C, true);
        cpu.rol(&Operand::Accumulator);
        assert_eq!(cpu.acc, 0b1001);
        assert!(!cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_rol_mem() {
        let mut cpu = CPU::new();
        cpu.load_ram(vec![0b10000000], 0);
        cpu.rol(&Operand::Address(0));
        assert_eq!(cpu.read_one(0), 0b00000000);
        assert!(cpu.get_status(Status::C));
        assert!(cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_ror_acc() {
        let mut cpu = CPU::new();
        cpu.acc = 0b001;
        cpu.set_status(Status::C, true);
        cpu.ror(&Operand::Accumulator);
        assert_eq!(cpu.acc, 0b10000000);
        assert!(cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(cpu.get_status(Status::S));
    }

    #[test]
    fn test_ror_mem() {
        let mut cpu = CPU::new();
        cpu.load_ram(vec![0b10000], 0);
        cpu.ror(&Operand::Address(0));
        assert_eq!(cpu.read_one(0), 0b1000);
        assert!(!cpu.get_status(Status::C));
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_rti() {
        let mut cpu = CPU::new();
        cpu.status = 3;
        cpu.pc = 0x0617;
        cpu.brk();
        cpu.rti();
        assert_eq!(cpu.sp, 0xFF);
        assert_eq!(cpu.pc, 0x0618);
        assert_eq!(cpu.status, 0b00110011);
    }

    #[test]
    fn test_rts() {
        let mut cpu = CPU::new();
        cpu.sp -= 2;
        cpu.mem[0x1FF] = 0x22;
        cpu.mem[0x1FE] = 0x11;
        cpu.rts();
        assert_eq!(cpu.sp, 0xFF);
        assert_eq!(cpu.pc, 0x2211 + 1);
    }

    #[test]
    fn test_sbc() {
        let mut cpu = CPU::new();
        let expecteds = vec![((80, 240, false), (95, false, false)),
                             ((80, 176, false), (159, false, true)),
                             ((80, 112, false), (223, false, false)),
                             ((80, 48, false), (31, true, false)),
                             ((208, 240, false), (223, false, false)),
                             ((208, 176, true), (32, true, false)),
                             ((208, 112, true), (96, true, true)),
                             ((208, 48, true), (160, true, false)),
                             ((255, 0, false), (254, true, false)),
                             ((0, 1, false), (254, false, false))];

        for expected in expecteds {
            let input = expected.0;
            let output = expected.1;
            cpu.acc = input.0;
            cpu.set_status(Status::C, input.2);
            cpu.set_status(Status::V, false);
            cpu.sbc(input.1);
            assert_eq!(cpu.acc, output.0, "computation");
            assert_eq!(cpu.get_status(Status::C), output.1, "carry");
            assert_eq!(cpu.get_status(Status::V), output.2, "overflow");
        }
    }

    #[test]
    fn test_sbc_decimal_mode() {
        let mut cpu = CPU::new();
        let expecteds = vec![((0x51, 0x21, false), (0x29, true, true)),
                             ((0x46, 0x12, true), (0x34, true, false)),
                             ((0x40, 0x13, true), (0x27, true, false)),
                             ((0x32, 0x02, false), (0x29, true, false))];

        for expected in expecteds {
            let input = expected.0;
            let output = expected.1;
            cpu.acc = input.0;
            cpu.set_status(Status::D, true);
            cpu.set_status(Status::C, input.2);
            cpu.set_status(Status::V, false);
            cpu.sbc(input.1);
            assert_eq!(cpu.acc, output.0, "computation");
            assert_eq!(cpu.get_status(Status::C), output.1, "carry");
            assert_eq!(cpu.get_status(Status::V), output.2, "overflow");
        }
    }

    #[test]
    fn test_setting() {
        let mut cpu = CPU::new();
        cpu.status = 0;
        cpu.sec();
        assert!(cpu.get_status(Status::C));
        cpu.sed();
        assert!(cpu.get_status(Status::D));
        cpu.sei();
        assert!(cpu.get_status(Status::I));
    }

    #[test]
    fn test_sta() {
        let mut cpu = CPU::new();
        cpu.acc = 10;
        cpu.sta(10);
        assert_eq!(cpu.mem[10], cpu.acc);
    }

    #[test]
    fn test_stx() {
        let mut cpu = CPU::new();
        cpu.x = 10;
        cpu.sta(10);
        assert_eq!(cpu.mem[10], cpu.acc);
    }

    #[test]
    fn test_sty() {
        let mut cpu = CPU::new();
        cpu.y = 10;
        cpu.sta(10);
        assert_eq!(cpu.mem[10], cpu.acc);
    }

    #[test]
    fn test_tax() {
        let mut cpu = CPU::new();
        cpu.acc = 10;
        cpu.tax();
        assert_eq!(cpu.acc, cpu.x);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_tay() {
        let mut cpu = CPU::new();
        cpu.acc = 10;
        cpu.tay();
        assert_eq!(cpu.acc, cpu.y);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_tsx() {
        let mut cpu = CPU::new();
        cpu.sp = 0xCD;
        cpu.tsx();
        assert_eq!(cpu.sp, cpu.x);
        assert!(!cpu.get_status(Status::Z));
        assert!(cpu.get_status(Status::S));
    }

    #[test]
    fn test_txa() {
        let mut cpu = CPU::new();
        cpu.x = 10;
        cpu.txa();
        assert_eq!(cpu.acc, cpu.x);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_txs() {
        let mut cpu = CPU::new();
        cpu.x = 10;
        cpu.txs();
        assert_eq!(cpu.x, cpu.sp);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    fn test_tya() {
        let mut cpu = CPU::new();
        cpu.y = 10;
        cpu.tya();
        assert_eq!(cpu.acc, cpu.y);
        assert!(!cpu.get_status(Status::Z));
        assert!(!cpu.get_status(Status::S));
    }

    #[test]
    #[ignore]
    // ignored because it is slow (> 60s)
    // be sure to run after making any changes to opcode handling
    fn test_functional() {
        let mut cpu = CPU::new();
        let mut code = Vec::new();
        let path = Path::new("test/binaries/klaus_test.bin");
        let mut file = File::open(path).unwrap();
        file.read_to_end(&mut code).unwrap();

        cpu.load_ram(code, 0);
        cpu.pc = 0x400;

        let pc_end = 0x3399; // end of all tests
        let mut pc_repeats = 0;
        while cpu.pc != pc_end {
            let byte = cpu.read_one(cpu.pc);
            let opcode = Opcode::get_by_code(byte).unwrap();
            let pc = cpu.pc;

            cpu.tick(opcode);

            if pc == cpu.pc {
                pc_repeats += 1;
            } else {
                pc_repeats = 0;
            }

            if pc_repeats > 5 {
                println!("stuck in trap at address: {:#04X}", cpu.pc);
                break;
            }
        }

        assert!(cpu.pc == pc_end);
    }
}
