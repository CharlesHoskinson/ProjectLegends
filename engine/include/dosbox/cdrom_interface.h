/*
 *  Copyright (C) 2002-2021  The DOSBox Team
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
 */

/**
 * @file cdrom_interface.h
 * @brief Public CD-ROM interface types for BIOS disk emulation
 *
 * This header provides the minimal public API for CD-ROM interfaces.
 * The full CDROM implementation is in engine/src/dos/cdrom.h (private).
 *
 * Module: aibox_core (public API)
 *
 * REFACTORING NOTE (Sprint 3):
 * Extracted from engine/src/dos/cdrom.h to provide clean module boundaries.
 * bios_disk.h now includes this public header instead of ../src/dos/cdrom.h.
 */

#ifndef DOSBOX_CDROM_INTERFACE_H
#define DOSBOX_CDROM_INTERFACE_H

#include <cstdint>
#include "mem.h"  // For PhysPt

/**
 * @brief CD-ROM time stamp (Minutes, Seconds, Frames)
 *
 * CD-ROM time is represented as minutes, seconds, and frames (75 frames per second).
 * This is the standard "Red Book" audio CD addressing format.
 */
struct TMSF {
    /** Time, minutes field */
    unsigned char min = 0;
    /** Time, seconds field */
    unsigned char sec = 0;
    /** Time, frame field (75 frames per second) */
    unsigned char fr = 0;
};

/**
 * @brief Output and channel control state for CD audio
 *
 * Controls audio output routing and volume for CD audio playback.
 */
struct TCtrl {
    /** Output channel mapping (4 channels) */
    uint8_t out[4];
    /** Channel volume levels (4 channels) */
    uint8_t vol[4];
};

/**
 * @brief Base CD-ROM interface class (abstract)
 *
 * This provides the base C++ class for CD-ROM interfaces in CD-ROM emulation.
 * Concrete implementations include SDL CD-ROM, image file (ISO/BIN+CUE), etc.
 */
class CDROM_Interface {
public:
    /** Interface type identifiers */
    enum INTERFACE_TYPE {
        ID_BASE = 0,
        ID_FAKE,
        ID_IMAGE
    };

    virtual ~CDROM_Interface() {}

    /** Set the device associated with this interface */
    virtual bool SetDevice(char* path, int forceCD) = 0;

    /** Get UPC string from the CD-ROM */
    virtual bool GetUPC(unsigned char& attr, char* upc) = 0;

    /** Retrieve start and end tracks and lead out position */
    virtual bool GetAudioTracks(int& stTrack, int& end, TMSF& leadOut) = 0;

    /** Retrieve start and attributes for a specific track */
    virtual bool GetAudioTrackInfo(int track, TMSF& start, unsigned char& attr) = 0;

    /** Get subchannel data and current position */
    virtual bool GetAudioSub(unsigned char& attr, unsigned char& track,
                            unsigned char& index, TMSF& relPos, TMSF& absPos) = 0;

    /** Get audio playback status */
    virtual bool GetAudioStatus(bool& playing, bool& pause) = 0;

    /** Get media tray status */
    virtual bool GetMediaTrayStatus(bool& mediaPresent, bool& mediaChanged, bool& trayOpen) = 0;

    /** Initiate audio playback starting at sector */
    virtual bool PlayAudioSector(unsigned long start, unsigned long len) = 0;

    /** Pause audio playback */
    virtual bool PauseAudio(bool resume) = 0;

    /** Stop audio playback */
    virtual bool StopAudio(void) = 0;

    /** Set channel control data */
    virtual void ChannelControl(TCtrl ctrl) = 0;

    /** Read sector data into guest memory */
    virtual bool ReadSectors(PhysPt buffer, bool raw, unsigned long sector, unsigned long num) = 0;

    /** Read sector data into host memory (for IDE emulation) */
    virtual bool ReadSectorsHost(void* buffer, bool raw, unsigned long sector, unsigned long num) = 0;

    /** Load (close/spin up) or unload (eject/spin down) media */
    virtual bool LoadUnloadMedia(bool unload) = 0;

    /** Initialize new media (called on disc change) */
    virtual void InitNewMedia(void) {}

    /** Interface type identifier */
    INTERFACE_TYPE class_id = ID_BASE;
};

/**
 * @brief Get MSCDEX drive interface
 *
 * Retrieves the CDROM_Interface for a given drive letter.
 * This function is defined in the DOS subsystem implementation.
 *
 * @param drive_letter Drive letter (0='A', 1='B', etc.)
 * @param _cdrom Output: pointer to the CDROM_Interface
 * @return true if drive is a valid MSCDEX drive
 */
bool GetMSCDEXDrive(unsigned char drive_letter, CDROM_Interface** _cdrom);

#endif /* DOSBOX_CDROM_INTERFACE_H */
