// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_MESSAGE_TYPES_H
#define LEGENDS_IPC_MESSAGE_TYPES_H

#include <cstdint>

namespace legends_ipc {

// Message type IDs. Each legends_embed.h function has a request/response pair.
// Control messages use 0x00xx, API messages use 0x01xx+.
enum class MsgType : uint16_t {
    // ── Control ──────────────────────────────────────────────────────────
    Handshake           = 0x0001,
    HandshakeAck        = 0x0002,
    Shutdown            = 0x0003,
    ShutdownAck         = 0x0004,
    Heartbeat           = 0x0005,
    HeartbeatAck        = 0x0006,
    ErrorResponse       = 0x0007,

    // ── Lifecycle ────────────────────────────────────────────────────────
    GetApiVersionReq    = 0x0100,
    GetApiVersionResp   = 0x0101,
    CreateReq           = 0x0102,
    CreateResp          = 0x0103,
    DestroyReq          = 0x0104,
    DestroyResp         = 0x0105,
    ForceDestroyReq     = 0x0106,
    ForceDestroyResp    = 0x0107,
    ResetReq            = 0x0108,
    ResetResp           = 0x0109,
    GetConfigReq        = 0x010A,
    GetConfigResp       = 0x010B,

    // ── Stepping ─────────────────────────────────────────────────────────
    StepMsReq           = 0x0200,
    StepMsResp          = 0x0201,
    StepCyclesReq       = 0x0202,
    StepCyclesResp      = 0x0203,
    GetEmuTimeReq       = 0x0204,
    GetEmuTimeResp      = 0x0205,
    GetTotalCyclesReq   = 0x0206,
    GetTotalCyclesResp  = 0x0207,

    // ── Frame capture ────────────────────────────────────────────────────
    CaptureTextReq      = 0x0300,
    CaptureTextResp     = 0x0301,
    CaptureRgbReq       = 0x0302,
    CaptureRgbResp      = 0x0303,
    IsFrameDirtyReq     = 0x0304,
    IsFrameDirtyResp    = 0x0305,
    GetCursorReq        = 0x0306,
    GetCursorResp       = 0x0307,

    // ── Input ────────────────────────────────────────────────────────────
    KeyEventReq         = 0x0400,
    KeyEventResp        = 0x0401,
    KeyEventExtReq      = 0x0402,
    KeyEventExtResp     = 0x0403,
    TextInputReq        = 0x0404,
    TextInputResp       = 0x0405,
    MouseEventReq       = 0x0406,
    MouseEventResp      = 0x0407,

    // ── Audio ────────────────────────────────────────────────────────────
    CaptureAudioReq     = 0x0500,
    CaptureAudioResp    = 0x0501,
    IsAudioActiveReq    = 0x0502,
    IsAudioActiveResp   = 0x0503,

    // ── Save/Load ────────────────────────────────────────────────────────
    SaveStateReq        = 0x0600,
    SaveStateResp       = 0x0601,
    LoadStateReq        = 0x0602,
    LoadStateResp       = 0x0603,
    GetStateHashReq     = 0x0604,
    GetStateHashResp    = 0x0605,
    VerifyDeterminismReq  = 0x0606,
    VerifyDeterminismResp = 0x0607,

    // ── Error/Log ────────────────────────────────────────────────────────
    GetLastErrorReq     = 0x0700,
    GetLastErrorResp    = 0x0701,
    SetLogCallbackReq   = 0x0702,
    SetLogCallbackResp  = 0x0703,

    // ── Drive Mounting ───────────────────────────────────────────────────
    MountDriveReq       = 0x0800,
    MountDriveResp      = 0x0801,
    UnmountDriveReq     = 0x0802,
    UnmountDriveResp    = 0x0803,

    // ── Video Capture ────────────────────────────────────────────────────
    StartVideoCaptureReq  = 0x0900,
    StartVideoCaptureResp = 0x0901,
    StopVideoCaptureReq   = 0x0902,
    StopVideoCaptureResp  = 0x0903,
    IsVideoCapturingReq   = 0x0904,
    IsVideoCapturingResp  = 0x0905,

    // ── Joystick ─────────────────────────────────────────────────────────
    JoystickEventReq    = 0x0A00,
    JoystickEventResp   = 0x0A01,

    // ── MIDI ─────────────────────────────────────────────────────────────
    MidiSetDeviceReq    = 0x0B00,
    MidiSetDeviceResp   = 0x0B01,
    MidiSetSoundfontReq = 0x0B02,
    MidiSetSoundfontResp = 0x0B03,
    MidiSetRomdirReq    = 0x0B04,
    MidiSetRomdirResp   = 0x0B05,
    CaptureMidiAudioReq = 0x0B06,
    CaptureMidiAudioResp = 0x0B07,

    // ── Printer ──────────────────────────────────────────────────────────
    PrinterSetOutputReq = 0x0C00,
    PrinterSetOutputResp = 0x0C01,
    PrinterIsActiveReq  = 0x0C02,
    PrinterIsActiveResp = 0x0C03,
    PrinterFlushReq     = 0x0C04,
    PrinterFlushResp    = 0x0C05,
    SetTtfFontReq       = 0x0C06,
    SetTtfFontResp      = 0x0C07,

    // ── IPX ──────────────────────────────────────────────────────────────
    IpxEnableReq        = 0x0D00,
    IpxEnableResp       = 0x0D01,
    IpxConnectReq       = 0x0D02,
    IpxConnectResp      = 0x0D03,
    IpxDisconnectReq    = 0x0D04,
    IpxDisconnectResp   = 0x0D05,
    IpxIsConnectedReq   = 0x0D06,
    IpxIsConnectedResp  = 0x0D07,

    // ── 3DFX Glide ───────────────────────────────────────────────────────
    GlideEnableReq      = 0x0E00,
    GlideEnableResp     = 0x0E01,
    GlideSetResolutionReq = 0x0E02,
    GlideSetResolutionResp = 0x0E03,

    // ── PC-98 ────────────────────────────────────────────────────────────
    SetMachinePc98Req   = 0x0F00,
    SetMachinePc98Resp  = 0x0F01,
    IsPc98ModeReq       = 0x0F02,
    IsPc98ModeResp      = 0x0F03,

    // ── Capabilities ─────────────────────────────────────────────────────
    HasCapabilityReq    = 0x1000,
    HasCapabilityResp   = 0x1001,

    // ── Events ───────────────────────────────────────────────────────────
    RegisterEventCallbackReq  = 0x1100,
    RegisterEventCallbackResp = 0x1101,
    EventNotification         = 0x1102,
};

} // namespace legends_ipc

#endif // LEGENDS_IPC_MESSAGE_TYPES_H
